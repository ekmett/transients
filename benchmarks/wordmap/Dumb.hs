{-# LANGUAGE CPP #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -fno-warn-orphans -fno-warn-type-defaults #-}
#ifdef ST_HACK
{-# OPTIONS_GHC -fno-full-laziness #-}
#endif
--------------------------------------------------------------------------------
-- |
-- Copyright   : (c) Edward Kmett 2015
-- License     : BSD-style
-- Maintainer  : Edward Kmett <ekmett@gmail.com>
-- Portability : non-portable
--
-- This module suppose a Word64-based array-mapped PATRICIA Trie.
--
-- The most significant nybble is isolated by using techniques based on
-- <https://www.fpcomplete.com/user/edwardk/revisiting-matrix-multiplication/part-4>
-- but modified to work nybble-by-nybble rather than bit-by-bit.
--
--------------------------------------------------------------------------------
module Dumb
  ( WordMap
  , singleton
  , empty
  , insert
  -- , delete
  , lookup
  , member
  , fromList
  ) where

import Control.Applicative hiding (empty)
import Control.DeepSeq
import Control.Lens
import Control.Monad.ST hiding (runST)
import Data.Bits
import Data.Transient.Primitive.SmallArray
import Data.Foldable
import Data.Functor
import Data.Monoid
import Data.Word
import qualified GHC.Exts as Exts
import Prelude hiding (lookup, length, foldr)
import GHC.Exts
import GHC.ST

type Key = Word64
type Mask = Word16
type Offset = Int

ptrEq :: a -> a -> Bool
ptrEq x y = isTrue# (Exts.reallyUnsafePtrEquality# x y Exts.==# 1#)
{-# INLINEABLE ptrEq #-}

ptrNeq :: a -> a -> Bool
ptrNeq x y = isTrue# (Exts.reallyUnsafePtrEquality# x y Exts./=# 1#)
{-# INLINEABLE ptrNeq #-}

data WordMap v
  = Nil
  | WordMap {-# UNPACK #-} !Key {-# UNPACK #-} !Offset !(Node v)
  deriving (Functor, Traversable)

instance Foldable WordMap where
  foldMap f (WordMap _ _ v) = foldMap f v
  foldMap _ Nil = mempty
  null Nil = True
  null _ = False

data Node v
  = Full {-# UNPACK #-} !(SmallArray (Node v))
  | Node {-# UNPACK #-} !Mask {-# UNPACK #-} !(SmallArray (Node v))
  | Tip  {-# UNPACK #-} !Key v
  deriving (Functor, Foldable, Traversable)
 
node :: Mask -> SmallArray (Node v) -> Node v
node 0xffff a = Full a
node m a      = Node m a
{-# INLINE node #-}

instance NFData v => NFData (WordMap v) where
  rnf (WordMap _ _ a) = rnf a
  rnf Nil           = ()

instance NFData v => NFData (Node v) where
  rnf (Full a)   = rnf a
  rnf (Node _ a) = rnf a
  rnf (Tip _ v)  = rnf v

instance AsEmpty (WordMap a) where
  _Empty = prism (const Nil) $ \s -> case s of
    Nil -> Right ()
    t -> Left t

type instance Index (WordMap a) = Word64
type instance IxValue (WordMap a) = a

instance Ixed (WordMap a) where
  ix i f m = case lookup i m of
    Just a -> f a <&> \a' -> insert i a' m
    Nothing -> pure m

{-
instance At (WordMap a) where
  at i f m = f (lookup i m) <&> \case
    Nothing -> delete i m
    Just a -> insert i a m
-}

-- Note: 'level 0' will return a negative shift, don't use it
level :: Key -> Int
level w = 60 - (countLeadingZeros w .&. 0x7c)
{-# INLINE level #-}

maskBit :: Key -> Offset -> Int
maskBit k o = fromIntegral (unsafeShiftR k o .&. 0xf)
{-# INLINE maskBit #-}

mask :: Key -> Offset -> Word16
mask k o = unsafeShiftL 1 (maskBit k o)
{-# INLINE mask #-}

pretty :: Key -> Int -> Key
pretty k o = k .&. unsafeShiftL 0xfffffffffffffff0 o 

fork :: Offset -> Key -> Node v -> Key -> Node v -> WordMap v
fork n k v ok ov = WordMap (pretty k n) n (runST $ bin n k v ok ov)

bin :: Offset -> Key -> Node v -> Key -> Node v -> ST s (Node v)
bin n k v ok ov 
  | b == ob = do
    !z  <- bin (n-4) k v ok ov 
    mas <- newSmallArray 1 z
    as  <- unsafeFreezeSmallArray mas
    return $ Node b as
  | otherwise = do
      mas <- newSmallArray 2 v
      writeSmallArray mas (fromEnum (k < ok)) ov
      as <- unsafeFreezeSmallArray mas
      return (Node (b .|. ob) as)
  where
    b = mask k n 
    ob = mask ok n 
  
insert :: Key -> v -> WordMap v -> WordMap v
insert k0 v0 Nil = WordMap (pretty k0 0) 0 (Tip k0 v0)
insert k0 v0 t@(WordMap ok0 n0 on0)
  | wd0 > 0xf = fork (level okk0) k0 (Tip k0 v0) ok0 on0
  | !r <- go k0 v0 n0 on0 
  , ptrNeq r on0 = WordMap ok0 n0 r
  | otherwise    = t
  where
    okk0 = xor ok0 k0
    wd0 = unsafeShiftR okk0 n0
    go !k !v !n on@(Tip ok ov)
      | k /= ok    = runST (bin n k (Tip k v) ok on)
      | ptrEq v ov = on
      | otherwise  = Tip k v
    go k v n on@(Full as)
      | ptrEq z oz = on
      | otherwise  = Full (update16 d z as)
      where
        d = maskBit k n
        !oz = indexSmallArray as d
        !z = go k v (n - 4) oz
    go k v n on@(Node m as)
      | m .&. b == 0                = node (m .|. b) (insertSmallArray p (Tip k v) as)
      | !oz <- indexSmallArray as p
      , !z <- go k v (n - 4) oz
      , ptrNeq z oz                 = Node m (updateSmallArray p z as)
      | otherwise                   = on
      where
        b = mask k n
        p = popCount $ m .&. (b-1)
{-# INLINEABLE insert #-}

lookup :: Key -> WordMap v -> Maybe v
lookup !_ Nil = Nothing
lookup k0 (WordMap ok0 n0 on0) 
  | wd0 > 0xf = Nothing
  | otherwise = go k0 n0 on0
  where
    okk0 = xor ok0 k0
    wd0 = unsafeShiftR okk0 n0
    go k _ (Tip ok ov)
      | k == ok = Just ov
      | otherwise = Nothing
    go k n (Full as) = go k (n-4) (indexSmallArray as (maskBit k n))
    go k n (Node m as)
      | m .&. b == 0 = Nothing
      | otherwise = go k (n-4) (indexSmallArray as p)
      where
        b = mask k n
        p = popCount $ m .&. (b-1)
{-# INLINE lookup #-}

member :: Key -> WordMap v -> Bool
member !_ Nil = False
member k0 (WordMap ok0 n0 on0) = wd0 <= 0xf && go k0 n0 on0
  where
    okk0 = xor ok0 k0
    wd0 = unsafeShiftR okk0 n0
    go k _ (Tip ok _) = k == ok 
    go k n (Full as) = go k (n-4) (indexSmallArray as (maskBit k n))
    go k n (Node m as) = m .&. b /= 0 && go k (n-4) (indexSmallArray as p)
      where
        b = mask k n
        p = popCount $ m .&. (b-1)
{-# INLINE member #-}
      
updateSmallArray :: Int -> a -> SmallArray a -> SmallArray a
updateSmallArray !k a i = runST $ do
  let n = length i
  o <- newSmallArray n undefined
  copySmallArray o 0 i 0 n
  writeSmallArray o k a
  unsafeFreezeSmallArray o
{-# INLINEABLE updateSmallArray #-}

update16 :: Int -> a -> SmallArray a -> SmallArray a
update16 !k a i = runST $ do
  o <- clone16 i
  writeSmallArray o k a
  unsafeFreezeSmallArray o
{-# INLINEABLE update16 #-}

insertSmallArray :: Int -> a -> SmallArray a -> SmallArray a
insertSmallArray !k a i = runST $ do
  let n = length i
  o <- newSmallArray (n + 1) a
  copySmallArray  o 0 i 0 k
  copySmallArray  o (k+1) i k (n-k)
  unsafeFreezeSmallArray o
{-# INLINEABLE insertSmallArray #-}

{-
deleteSmallArray :: Int -> SmallArray a -> SmallArray a
deleteSmallArray !k i = runST $ do
  let n = length i
  o <- newSmallArray (n - 1) undefined
  copySmallArray o 0 i 0 k
  copySmallArray o k i (k+1) (n-k-1)
  unsafeFreezeSmallArray o
{-# INLINEABLE deleteSmallArray #-}
-}

clone16 :: SmallArray a -> ST s (SmallMutableArray s a)
clone16 i = do
  o <- newSmallArray 16 undefined
  indexSmallArrayM i 0 >>= writeSmallArray o 0
  indexSmallArrayM i 1 >>= writeSmallArray o 1
  indexSmallArrayM i 2 >>= writeSmallArray o 2
  indexSmallArrayM i 3 >>= writeSmallArray o 3
  indexSmallArrayM i 4 >>= writeSmallArray o 4
  indexSmallArrayM i 5 >>= writeSmallArray o 5
  indexSmallArrayM i 6 >>= writeSmallArray o 6
  indexSmallArrayM i 7 >>= writeSmallArray o 7
  indexSmallArrayM i 8 >>= writeSmallArray o 8
  indexSmallArrayM i 9 >>= writeSmallArray o 9
  indexSmallArrayM i 10 >>= writeSmallArray o 10
  indexSmallArrayM i 11 >>= writeSmallArray o 11
  indexSmallArrayM i 12 >>= writeSmallArray o 12
  indexSmallArrayM i 13 >>= writeSmallArray o 13
  indexSmallArrayM i 14 >>= writeSmallArray o 14
  indexSmallArrayM i 15 >>= writeSmallArray o 15
  return o
{-# INLINE clone16 #-}

-- | Build a singleton WordMap
singleton :: Key -> v -> WordMap v
singleton k v = WordMap (pretty k 0) 0 (Tip k v)
{-# INLINE singleton #-}

instance FunctorWithIndex Word64 WordMap where
  imap _ Nil = Nil
  imap f (WordMap k n o) = WordMap k n (imap f o)

instance FunctorWithIndex Word64 Node where
  imap f (Node m  as) = Node m (fmap (imap f) as)
  imap f (Tip k v) = Tip k (f k v)
  imap f (Full as) = Full (fmap (imap f) as)

instance FoldableWithIndex Word64 WordMap where
  ifoldMap _ Nil = mempty
  ifoldMap f (WordMap _ _ o) = ifoldMap f o

instance FoldableWithIndex Word64 Node where
  ifoldMap f (Node _ as) = foldMap (ifoldMap f) as
  ifoldMap f (Tip k v) = f k v
  ifoldMap f (Full as) = foldMap (ifoldMap f) as

instance TraversableWithIndex Word64 WordMap where
  itraverse f (WordMap k n o) = WordMap k n <$> itraverse f o
  itraverse _ Nil = pure Nil

instance TraversableWithIndex Word64 Node where
  itraverse f (Node m as) = Node m <$> traverse (itraverse f) as
  itraverse f (Tip k v) = Tip k <$> f k v
  itraverse f (Full as) = Full <$> traverse (itraverse f) as

instance IsList (WordMap v) where
  type Item (WordMap v) = (Word64, v)

  toList = ifoldr (\i a r -> (i, a): r) []
  {-# INLINE toList #-}

  fromList xs = foldl' (\r (k,v) -> insert k v r) Nil xs
  {-# INLINE fromList #-}

  fromListN _ = fromList
  {-# INLINE fromListN #-}

empty :: WordMap a
empty = Nil
{-# INLINE empty #-}
