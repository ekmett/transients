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
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -fno-warn-orphans -fno-warn-type-defaults -O2 -fobject-code #-}
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
-- This variant tries to flatten the tree as much as possible by using unsafe indexing tricks
-- to pack the tip nodes directly into their parent, thereby removing a level of indirection
--
--------------------------------------------------------------------------------
module FlatMap
  ( WordMap
  , singleton
  , empty
  , lookup
  , insert
  ) where

import Control.Applicative hiding (empty)
import Control.DeepSeq
import Control.Exception
import Control.Lens
import Control.Monad.ST hiding (runST)
import Data.Bits
import Data.Transient.Primitive.Exts ()
import Data.Transient.Primitive.SmallArray
import Data.Foldable as Foldable hiding (any)
import Data.Functor
import Data.Monoid hiding (Any)
import Data.Primitive
import Data.Word
import qualified GHC.Exts as Exts
import Prelude hiding (lookup, length, foldr, any)
import GHC.Exts as Exts
import GHC.ST
import Unsafe.Coerce

type Key = Word64
type Mask = Word16
type Offset = Int

ptrEq :: a -> a -> Bool
ptrEq x y = isTrue# (Exts.reallyUnsafePtrEquality# x y Exts.==# 1#)
{-# INLINEABLE ptrEq #-}

data WordMap v = Node !Word64 !Offset !Mask !Mask !ByteArray !(SmallArray Any)

instance Show a => Show (WordMap a) where
  showsPrec d m = showParen (d > 10) $ showString "fromList " . showsPrec 11 (Exts.toList m)

empty :: WordMap a
empty = Node 0 0 0 0 mempty mempty

instance NFData v => NFData (WordMap v) where
  rnf (Node _ _ m0 t _ as) = go m0 0 `seq` () where
    n = length as
    go :: Word16 -> Int -> ()
    go !m !i
      | i >= n = ()
      | any <- indexSmallArray as i 
      = (if tippy m t then rnf (unsafeCoerce any :: v) else rnf (unsafeCoerce any :: WordMap v)) `seq` go (clear m) (i+1)

tippy :: Word16 -> Word16 -> Bool
tippy m t = m .&. negate m .&. t /= 0

clear :: Word16 -> Word16
clear m = m .&. (m - 1)

instance Functor WordMap where
  fmap (f :: a -> b) (Node ok o m0 t bs as) = Node ok o m0 t bs $ runST $ do
    out <- newSmallArray (length as) undefined
    go out m0 0
    where
      n = length as
      go :: SmallMutableArray s Any -> Word16 -> Int -> ST s (SmallArray Any)
      go out !m !i 
        | i < n = do
          x <- indexSmallArrayM as i
          if tippy m t
            then writeSmallArray out i (unsafeCoerce (f (unsafeCoerce x :: a)))
            else writeSmallArray out i $! unsafeCoerce (fmap f (unsafeCoerce x :: WordMap a))
          go out (clear m) (i+1)
        | otherwise = unsafeFreezeSmallArray out

instance FunctorWithIndex Word64 WordMap where
  imap (f :: Word64 -> a -> b) (Node ok o m0 t bs as) = Node ok o m0 t bs $ runST $ do
    out <- newSmallArray (length as) undefined
    go out m0 0 0
    where
      n = length as
      go :: SmallMutableArray s Any -> Word16 -> Int -> Int -> ST s (SmallArray Any)
      go out !m !i !j
        | i < n = do
          x <- indexSmallArrayM as i
          if tippy m t
            then do
              writeSmallArray out i (unsafeCoerce (f (indexByteArray bs j) (unsafeCoerce x :: a)))
              go out (clear m) (i+1) (j+1)
            else do
              writeSmallArray out i $! unsafeCoerce (imap f (unsafeCoerce x :: WordMap a))
              go out (clear m) (i+1) j
        | otherwise = unsafeFreezeSmallArray out

sIZEOF_WORD64 :: Int
sIZEOF_WORD64 = sizeOf (0 :: Word64)

instance Foldable WordMap where
  foldMap (f :: a -> m) (Node _ _ m0 t _ as) = go m0 0 where
    n = length as
    go :: Word16 -> Int -> m
    go !m !i
      | i >= n = mempty
      | tippy m t = (if tippy m t then f (unsafeCoerce any) else foldMap f (unsafeCoerce any :: WordMap a)) `mappend` go (clear m) (i + 1)
      where any = indexSmallArray as i 
  null (Node _ _ m _ _ _) = m == 0

instance FoldableWithIndex Word64 WordMap where
  ifoldMap (f :: Word64 -> a -> m) (Node _ _ m0 t bs as) = go m0 0 0 where
    n = length as
    go :: Word16 -> Int -> Int -> m
    go !m !i !j
      | i >= n    = mempty
      | tippy m t = f (indexByteArray bs j) (unsafeCoerce any) `mappend` go (clear m) (i + 1) (j+1)
      | otherwise = ifoldMap f (unsafeCoerce any :: WordMap a) `mappend` go (clear m) (i + 1) j
      where any = indexSmallArray as i

singleton :: Word64 -> a -> WordMap a
singleton k a = Node k 0 m m bs (fromList [unsafeCoerce a]) where
  m = unsafeShiftL 1 (fromIntegral (k .&. 0xf))
  bs = runST $ do
    o <- newByteArray (sizeOf k)
    writeByteArray o 0 k
    unsafeFreezeByteArray o

-- Note: 'level 0' will return a negative shift, don't use it
level :: Key -> Key -> Int
level u v = 60 - (countLeadingZeros (xor u v) .&. 0x7c)
{-# INLINE level #-}

nybbleBit :: Key -> Offset -> Int
nybbleBit k o = fromIntegral (unsafeShiftR k o .&. 0xf)
{-# INLINE nybbleBit #-}

nybble :: Key -> Offset -> Word16
nybble k o = unsafeShiftL 1 (nybbleBit k o)
{-# INLINE nybble #-}

lookup :: Key -> WordMap v -> Maybe v
lookup !_ (Node _ _ 0 _ _ _) = Nothing
lookup k0 n0 = go k0 n0 where
  go !k (Node ok o m t bs as) 
    | wz > 0xf = Nothing
    -- accelerate the full case
    | 0xffff <- m, any <- indexSmallArray as z = if
      | t .&. b == 0 -> lookup k (unsafeCoerce any)
      | indexByteArray bs z == k -> Just (unsafeCoerce any) 
      | otherwise -> Nothing
    | m .&. b /= 0, pz <- popCount (m .&. (b-1)), any <- indexSmallArray as pz = if
      | t .&. b == 0 -> lookup k (unsafeCoerce any)
      | indexByteArray bs (popCount (t .&. (b-1))) == k -> Just (unsafeCoerce any)
      | otherwise -> Nothing
    | otherwise = Nothing
    where wz = xor (unsafeShiftR ok o .&. complement 0xf) (unsafeShiftR k o)
          z = fromIntegral wz
          b = unsafeShiftL 1 z
{-# INLINEABLE lookup #-}

unsafeCoerce1 :: f a -> f b
unsafeCoerce1 = unsafeCoerce

fork :: Offset -> Mask -> Mask -> Key -> Any -> Key -> Any -> ST s (WordMap v)
fork o m t k n ok on = do
  mbs <- newByteArray (2*sIZEOF_WORD64)
  mas <- newSmallArray 2 n
  let i = fromEnum (k < ok)
  writeByteArray mbs (1-i) k
  writeByteArray mbs i ok
  writeSmallArray mas i on
  Node k o m t <$> unsafeFreezeByteArray mbs <*> unsafeFreezeSmallArray mas

-- fork with two child tips
forkTip2 :: Offset -> Key ->  v -> Key -> v -> ST s (WordMap v)
forkTip2 o k v ok ov = unsafeCoerce1 fork o m m k v ok ov
  where m = nybble k o .|. nybble ok o
  
-- fork where one child is known to be a tip, and the other is any node below the fork
forkTip :: Key -> v -> Key -> WordMap v -> ST s (WordMap v)
forkTip k v ok on@(Node _ _ _ t _ as)
  | length as == 1 = assert (t /= 0) $ do -- this is a standalone, fat, tip
     ov <- indexSmallArrayM as 0
     unsafeCoerce1 forkTip2 o k v ok ov
  | t' <- nybble k o = unsafeCoerce1 fork o (t' .|. nybble ok o) t' k v ok on
  where o = level k ok
  
insert :: forall v. Key -> v -> WordMap v -> WordMap v
insert !k v (Node _ _ 0 _ _ _) = singleton k v -- the empty case only happens at the root
insert k v n0 = runST $ go n0 where
  go :: WordMap v -> ST s (WordMap v)
  go on@(Node ok o m t bs as)
    | wd > 0xf = forkTip k v ok on -- fork above our level
    | m == 0xffff = part update16 d -- accelerate updates that apply to a full node -- removable
    | odm <- popCount $ m .&. (b-1) = if -- partial node
      | m .&. b == 0 -> return $ Node ok o (m .|. b) (t .|. b) (insertByteArray odt k bs) (unsafeCoerce insertSmallArray odm v as) -- add child tip
      | otherwise    -> part updateSmallArray odm -- update an existing child branch
    where 
      part :: (Int -> a -> SmallArray Any -> SmallArray Any) -> Int -> ST s (WordMap v)
      part update odm 
        | t .&. b /= 0 = do -- updating a child tip
          tv <- unsafeCoerce1 (indexSmallArrayM as odm)
          if
            | tk <- indexByteArray bs odt, k /= tk -> do
              ti <- forkTip2 (level tk k) k v tk tv
              return $ Node ok o m (t .&. complement b) bs (unsafeCoerce update odm ti as)
            | ptrEq v tv -> return on -- nothing changed, optimization, removable
            | otherwise -> return $ Node ok o m t bs (unsafeCoerce update odm v as) -- rewrite tip
        | otherwise = do
          !oz <- unsafeCoerce1 (indexSmallArrayM as odm)
          !z <- go oz
          return $ if
            | ptrEq oz z -> on -- optimization, removable
            | otherwise -> Node ok o m t bs (unsafeCoerce update odm z as) -- updated non-tip child, remains non-tip
      wd = xor (unsafeShiftR ok o .&. complement 0xf) (unsafeShiftR k o)
      d  = fromIntegral wd
      b  = unsafeShiftL 1 d
      odt = popCount $ t .&. (b-1)
{-# INLINEABLE insert #-}

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

-- byte offset
insertByteArray :: Int -> Word64 -> ByteArray -> ByteArray
insertByteArray !k a i = runST $ do
  let n = sizeofByteArray i
  let s = sizeOf a 
  o <- newByteArray (n + s)
  let ks = k * s
  copyByteArray  o 0 i 0 ks
  writeByteArray o k a
  copyByteArray  o (ks+s) i ks (n-ks)
  unsafeFreezeByteArray o
{-# INLINEABLE insertByteArray #-}

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

instance IsList (WordMap v) where
  type Item (WordMap v) = (Word64, v)

  toList = ifoldr (\i a r -> (i, a): r) []
  {-# INLINE toList #-}

  fromList xs = foldl' (\r (k,v) -> insert k v r) empty xs
  {-# INLINE fromList #-}

  fromListN _ = fromList
  {-# INLINE fromListN #-}

instance AsEmpty (WordMap a) where
  _Empty = prism (const empty) $ \s -> case s of
    Node _ _ 0 _ _ _ -> Right ()
    t -> Left t

type instance Index (WordMap a) = Word64
type instance IxValue (WordMap a) = a

instance Ixed (WordMap a) where
  ix i f m = case lookup i m of
    Just a -> f a <&> \a' -> insert i a' m
    Nothing -> pure m
