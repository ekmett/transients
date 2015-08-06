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
{-# LANGUAGE UnboxedTuples #-}
{-# OPTIONS_GHC -fno-warn-orphans -fno-warn-type-defaults -fobject-code #-}
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
-- This structure secretly maintains a finger to the previous mutation to
-- speed access and repeated operations.
--
--------------------------------------------------------------------------------
module Fingered
{-
  ( Node
  , singleton
  , empty
  , insert
  , delete
  , lookup
  -- , member
  , fromList
  ) -} where

import Control.Applicative hiding (empty)
import Control.DeepSeq
import Control.Lens hiding (index)
import Control.Monad.ST hiding (runST)
import Control.Monad.Primitive
import Data.Bits
import Data.Transient.Primitive.SmallArray
import Data.Foldable
import Data.Functor
import Data.Monoid
import Data.Word
import Debug.Trace
import qualified GHC.Exts as Exts
import Prelude hiding (lookup, length, foldr)
import GHC.Exts
import GHC.ST
import GHC.Word

type Key = Word64
type Mask = Word16
type Offset = Int

--------------------------------------------------------------------------------
-- * Utilities
--------------------------------------------------------------------------------

ptrEq :: a -> a -> Bool
ptrEq x y = isTrue# (Exts.reallyUnsafePtrEquality# x y Exts.==# 1#)
{-# INLINEABLE ptrEq #-}

ptrNeq :: a -> a -> Bool
ptrNeq x y = isTrue# (Exts.reallyUnsafePtrEquality# x y Exts./=# 1#)
{-# INLINEABLE ptrNeq #-}

index :: Word16 -> Word16 -> Int
index m b = popCount (m .&. (b-1))
{-# INLINE index #-}

-- | Note: @level (xor k ok)@ will return a negative shift, don't use it
level :: Key -> Int
level okk = 60 - (countLeadingZeros okk .&. 0x7c)
{-# INLINE level #-}

maskBit :: Key -> Offset -> Int
maskBit k o = fromIntegral (unsafeShiftR k o .&. 0xf)
{-# INLINE maskBit #-}

mask :: Key -> Offset -> Word16
mask k o = unsafeShiftL 1 (maskBit k o)
{-# INLINE mask #-}

-- | Given a pair of keys, they agree down to this height in the display, don't use this when they are the same
-- 
-- @
-- apogeeBit k ok = unsafeShiftR (level (xor k ok)) 2
-- level (xor k ok) = unsafeShiftL (apogeeBit k ok) 2
-- @
apogeeBit :: Key -> Key -> Int
apogeeBit k ok = 15 - unsafeShiftR (countLeadingZeros (xor k ok)) 2

apogee :: Key -> Key -> Mask
apogee k ok = unsafeShiftL 1 (apogeeBit k ok) 

--------------------------------------------------------------------------------
-- * WordMap
--------------------------------------------------------------------------------

data Path v = Path {-# UNPACK #-} !Key {-# UNPACK #-} !Word16 {-# UNPACK #-} !(SmallArray (Node v))
  deriving (Functor, Foldable, Traversable, Show)

-- TODO: add a lazy (Node v) for canonical access?
-- TODO: fold/traverse in the "proper" order rather than leak the current finger location
data WordMap v = WordMap !(Path v) !(Maybe v)
  deriving (Functor,Foldable,Traversable,Show)

empty :: WordMap v
empty = WordMap (Path 0 0 mempty) Nothing

-- | Build a singleton Node
singleton :: Key -> v -> WordMap v
singleton k v = WordMap (Path k 0 mempty) (Just v)
{-# INLINE singleton #-}

-- we can broadcast the key, then compare in parallel with SWAR techniques
-- then we just have to search the appropriate array entries on down

data Node v
  = Full {-# UNPACK #-} !Key {-# UNPACK #-} !Offset {-# UNPACK #-} !(SmallArray (Node v))
  | Node {-# UNPACK #-} !Key {-# UNPACK #-} !Offset {-# UNPACK #-} !Mask {-# UNPACK #-} !(SmallArray (Node v))
  | Stub {-# UNPACK #-} !Key {-# UNPACK #-} !Offset !(Node v)
  | Tip  {-# UNPACK #-} !Key v
  | Nil -- only used in canonical form
  deriving (Functor,Foldable,Traversable,Show)
  -- TODO: manual Foldable

--------------------------------------------------------------------------------
-- * Lookup
--------------------------------------------------------------------------------

lookup :: Word64 -> WordMap v -> Maybe v
lookup k0 m0 = case m0 of
  WordMap (Path ok m ns) mv
    | k0 == ok -> mv
    | b <- apogee k0 ok -> if
      | m .&. b == 0 -> Nothing
      | otherwise -> go k0 (indexSmallArray ns (index m b))
  where
    go !k (Full ok o a)
      | z > 0xf = Nothing
      | otherwise = go k (indexSmallArray a (fromIntegral z))
      where z = unsafeShiftR (xor k ok) o
    go k (Node ok o m a)
      | z > 0xf      = Nothing
      | m .&. b == 0 = Nothing
      | otherwise = go k (indexSmallArray a (index m b))
      where z = unsafeShiftR (xor k ok) o
            b = unsafeShiftL 1 (fromIntegral z)
    go k (Stub ok o on)
      | z > 0xf   = Nothing
      | otherwise = go k on
      where z = unsafeShiftR (xor k ok) o
    go k (Tip ok ov)
      | k == ok   = Just ov
      | otherwise = Nothing
    go _ Nil      = Nothing
{-# INLINEABLE lookup #-}

--------------------------------------------------------------------------------
-- * Construction
--------------------------------------------------------------------------------

node :: Key -> Offset -> Mask -> SmallArray (Node v) -> Node v
node k o 0xffff a = Full k o a
node k o m a      = Node k o m a
{-# INLINE node #-}

fork :: Int -> Key -> Node v -> Key -> Node v -> Node v
fork o k n ok on = Node (k .&. unsafeShiftL 0xfffffffffffffff0 o) o (mask k o .|. mask ok o) $ runST $ do
  arr <- newSmallArray 2 n
  writeSmallArray arr (fromEnum (k < ok)) on
  unsafeFreezeSmallArray arr

-- O(1) plug a child node directly into an open parent node
-- carefully retains identity in case we plug what is already there back in
plug :: Key -> Node v -> Node v -> Node v
-- TODO: if we're plugging Nil in we need to roll this up gracefully
plug !k Nil on@(Node ok n m as) 
  | m .&. b == 0 = on
  | otherwise = Node ok n (m .&. complement b) (deleteSmallArray (index m b) as)
  where !b = unsafeShiftL 1 (fromIntegral (unsafeShiftR (xor k ok) n))
plug k z on@(Node ok n m as)
  | m .&. b == 0 = node ok n (m .|. b) (insertSmallArray odm z as)
  | !oz <- indexSmallArray as odm
  , ptrNeq z oz = Node ok n m (updateSmallArray odm z as)
  | otherwise   = on
  where !b   = unsafeShiftL 1 (fromIntegral (unsafeShiftR (xor k ok) n))
        !odm = index m b
plug k Nil (Full ok n as) = Node ok n (complement (unsafeShiftL 1 d)) (deleteSmallArray d as)
  where !d = fromIntegral (unsafeShiftR (xor k ok) n)
plug k z on@(Full ok n as)
  | !oz <- indexSmallArray as d
  , ptrNeq z oz = Full ok n (update16 d z as)
  | otherwise   = on
  where !d = fromIntegral (unsafeShiftR (xor k ok) n)
plug k Nil (Stub _ _ on)  = on
plug k z   (Stub ok n on) = fork n k z ok on
plug _ _   Tip{} = error "plug: unexpected Tip"
plug _ _   Nil   = error "plug: unexpected Nil"

-- | Given @k@ located under @acc@, @plugPath k i t acc ns@ plugs acc recursively into each of the nodes
-- of @ns@ from @[i..t-1]@ from the bottom up
plugPath :: Key -> Int -> Int -> Node v -> SmallArray (Node v) -> Node v
plugPath !k !i !t !acc !ns
  | i < t     = plugPath k (i+1) t (plug k acc (indexSmallArray ns i)) ns
  | otherwise = acc
  
unI# :: Int -> Int#
unI# (I# i) = i

-- create a 1-hole context at key k, destroying any previous contents of that position.
path :: Key -> WordMap v -> Path v
path k0 (WordMap p0@(Path ok0 m0 ns0@(SmallArray ns0#)) mv0)
  | k0 == ok0 = p0
  | n0 <- level (xor ok0 k0)
  , aok <- unsafeShiftR n0 2
  , kept <- m0 .&. unsafeShiftL 0xfffe aok
  , nkept@(I# nkept#) <- popCount kept -- max (popCount kept - 1) 0 
  , !top@(I# top#) <- length ns0 - nkept
  = runST $ primitive $ \s -> case go k0 (unI# n0) (plugPath k0 0 top (maybe Nil (Tip k0) mv0) ns0) s of
    (# s', ms, m# #) -> case copySmallArray# ns0# top# ms (sizeofSmallMutableArray# ms -# nkept#) nkept# s' of -- we're copying nkept
      s'' -> case unsafeFreezeSmallArray# ms s'' of
        (# s''', spine #) -> (# s''', Path k0 (kept .|. W16# m#) (SmallArray spine) #) 
  where
    cont1 :: Key -> Int# -> SmallArray# (Node v) -> Int# -> Node v -> Int# -> State# s -> 
      (# State# s, SmallMutableArray# s (Node v), Word# #)
    cont1 k h# as d# on n# s = case indexSmallArray# as d# of
      (# on' #) -> case go k (h# +# 1#) on' s of
        (# s', ms, m# #) -> cont2 ms h# on n# m# s'

    cont2 :: SmallMutableArray# s (Node v) -> Int# -> Node v -> Int# -> Word# -> State# s -> 
      (# State# s, SmallMutableArray# s (Node v), Word# #)
    cont2 ms h# on n# m# s = case writeSmallArray# ms (sizeofSmallMutableArray# ms -# h#) on s of -- we need to write into the bottom, not the top
      s' -> case unsafeShiftL 1 (unsafeShiftR (I# n#) 2) .|. W16# m# of
        W16# m'# -> (# s', ms, m'# #)

    cont3 :: SmallMutableArray# s (Node v) -> Int# -> Node v -> Int# -> State# s -> 
      (# State# s, SmallMutableArray# s (Node v), Word# #)
    cont3 ms h# on n# s = case writeSmallArray# ms (sizeofSmallMutableArray# ms -# h#) on s of -- we need to write into the bottom, not the top
      s' -> case unsafeShiftL 1 (unsafeShiftR (I# n#) 2) of
        W16# m'# -> (# s', ms, m'# #)

    go :: Key -> Int# -> Node v -> State# s -> (# State# s, SmallMutableArray# s (Node v), Word# #)
    go k h# on@(Full ok n@(I# n#) (SmallArray as)) s 
      | wd <= 0xf = cont1 k h# as (unI# (fromIntegral wd)) on n# s
      | otherwise = case newSmallArray# (h# +# 1#) undefined s of
        (# s', ms #) -> cont3 ms h# on n# s'
      where wd = unsafeShiftR (xor k ok) n
    go k h# on@(Node ok n@(I# n#) m (SmallArray as)) s
      | m .&. b /= 0 = cont1 k h# as (unI# (index m b)) on n# s
      | otherwise = case newSmallArray# (h# +# 1#) undefined s of
        (# s', ms #)
          | b == 0    -> cont3 ms h# (Stub ok (level okk) on) n# s'
          | otherwise -> cont3 ms h# on n# s'
      where okk = xor k ok
            b = shiftL 1 (fromIntegral (unsafeShiftR (xor k ok) n))
    go k h# on@(Tip ok ov) s
      | k == ok = case newSmallArray# h# undefined s of
        (# s', ms #) -> (# s', ms, int2Word# 0# #) 
      | otherwise = case newSmallArray# (h# +# 1#) undefined s of 
        (# s', ms #) -> let n = level (xor k ok) in cont3 ms h# (Stub ok n on) (unI# n) s'
    go k h# Nil s = case newSmallArray# h# undefined s of
      (# s', ms #) -> (# s', ms, int2Word# 0# #)
    go _ _ Stub{} _ = error "path: unexpected Stub"

insert :: Key -> v -> WordMap v -> WordMap v
insert k v wm@(WordMap p@(Path ok _ _) mv) 
  | k == ok, Just ov <- mv, ptrEq v ov = wm
  | otherwise = WordMap (path k wm) (Just v)

delete :: Key -> WordMap v -> WordMap v
delete k m = WordMap (path k m) Nothing

--------------------------------------------------------------------------------
-- * Instances
--------------------------------------------------------------------------------

type instance Index (WordMap a) = Word64
type instance IxValue (WordMap a) = a

instance At (WordMap v) where
  at k f wm@(WordMap p@(Path ok _ _) mv)
    | k == ok = WordMap p <$> f mv
    | otherwise = let c = path k wm in WordMap c <$> f (lookup k wm)
  {-# INLINE at #-}

instance Ixed (WordMap v) where
  ix k f wm = case lookup k wm of
    Nothing -> pure wm
    Just v -> let c = path k wm in f v <&> \v' -> WordMap c (Just v')

instance NFData v => NFData (Node v) where
  rnf (Full _ _ a)   = rnf a
  rnf (Node _ _ _ a) = rnf a
  rnf (Tip _ v)      = rnf v
  rnf (Stub _ _ n)   = rnf n
  rnf Nil            = ()

instance NFData v => NFData (WordMap v) where
  rnf (WordMap (Path _ _ as) mv) = rnf as `seq` rnf mv

instance AsEmpty (WordMap a) where
  _Empty = prism (const empty) $ \s -> case s of
    WordMap (Path _ 0 _) Nothing -> Right ()
    t -> Left t


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

deleteSmallArray :: Int -> SmallArray a -> SmallArray a
deleteSmallArray !k i = runST $ do
  let n = length i
  o <- newSmallArray (n - 1) undefined
  copySmallArray o 0 i 0 k
  copySmallArray o k i (k+1) (n-k-1)
  unsafeFreezeSmallArray o
{-# INLINEABLE deleteSmallArray #-}

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


instance FunctorWithIndex Word64 WordMap where
  imap f (WordMap (Path k n as) mv) = WordMap (Path k n (fmap (imap f) as)) (fmap (f k) mv)

instance FunctorWithIndex Word64 Node where
  imap f (Node k n m as) = Node k n m (fmap (imap f) as)
  imap f (Tip k v) = Tip k (f k v)
  imap _ Nil = Nil
  imap f (Full k n as) = Full k n (fmap (imap f) as)
  imap f (Stub k n a) = Stub k n (imap f a)

instance FoldableWithIndex Word64 WordMap where
  ifoldMap f (WordMap (Path k _ as) mv) = foldMap (f k) mv `mappend` foldMap (ifoldMap f) as

instance FoldableWithIndex Word64 Node where
  ifoldMap f (Node _ _ _ as) = foldMap (ifoldMap f) as
  ifoldMap f (Tip k v) = f k v
  ifoldMap _ Nil = mempty
  ifoldMap f (Full _ _ as) = foldMap (ifoldMap f) as
  ifoldMap f (Stub _ _ a) = ifoldMap f a

instance IsList (WordMap v) where
  type Item (WordMap v) = (Word64, v)

  toList = ifoldr (\i a r -> (i, a): r) []
  {-# INLINE toList #-}

  fromList xs = foldl' (\r (k,v) -> insert k v r) empty xs
  {-# INLINE fromList #-}

  fromListN _ = fromList
  {-# INLINE fromListN #-}
