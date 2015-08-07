{-# LANGUAGE CPP #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ViewPatterns #-}
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
  ( WordMap
  , singleton
  , empty
  , insert
  , delete
  , lookup
  , focus
  , fromList
  , Exts.toList
  , Key
  ) where

import Control.Applicative hiding (empty)
import Control.DeepSeq
import Control.Lens hiding (index, deep)
import Control.Monad
import Control.Monad.ST hiding (runST)
import Control.Monad.Primitive
import Data.Bits
import Data.Foldable
import Data.Monoid
import Data.Transient.Primitive.SmallArray
import Data.Word
import qualified GHC.Exts as Exts
import Prelude hiding (lookup, length, foldr)
import GHC.Exts as Exts
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

data WordMap v = WordMap !(Path v) !(Maybe v)
  deriving (Functor,Traversable,Show)

focus :: Key -> WordMap v -> WordMap v
focus k m = WordMap (path k m) (lookup k m)

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
  | Tip  {-# UNPACK #-} !Key v
  deriving (Functor,Foldable,Traversable,Show)
  -- TODO: manual Foldable

--------------------------------------------------------------------------------
-- * Lookup
--------------------------------------------------------------------------------

lookup :: Key -> WordMap v -> Maybe v
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
    go k (Tip ok ov)
      | k == ok   = Just ov
      | otherwise = Nothing
{-# INLINEABLE lookup #-}

--------------------------------------------------------------------------------
-- * Construction
--------------------------------------------------------------------------------

node :: Key -> Offset -> Mask -> SmallArray (Node v) -> Node v
node k o 0xffff a = Full k o a
node k o m a      = Node k o m a
{-# INLINE node #-}

fork :: Key -> Node v -> Key -> Node v -> Node v
fork k n ok on = Node (k .&. unsafeShiftL 0xfffffffffffffff0 o) o (mask k o .|. mask ok o) $ runST $ do
    arr <- newSmallArray 2 n
    writeSmallArray arr (fromEnum (k < ok)) on
    unsafeFreezeSmallArray arr
  where o = level (xor k ok)

-- O(1) remove the _entire_ branch containing a given node from this tree.
unplug :: Key -> Node v -> Node v
unplug k on@(Full ok n as)
  | wd >= 0xf = on
  | d <- fromIntegral wd = Node ok n (complement (unsafeShiftL 1 d)) (deleteSmallArray d as)
  where !wd = unsafeShiftR (xor k ok) n
unplug !k on@(Node ok n m as)
  | wd >= 0xf = on
  | !b <- unsafeShiftL 1 (fromIntegral wd), m .&. b /= 0, p <- index m b =
    if length as == 2
     then indexSmallArray as (1-p) -- keep the other node
     else Node ok n (m .&. complement b) (deleteSmallArray p as)
  | otherwise = on
  where !wd = unsafeShiftR (xor k ok) n
unplug _ on = on -- Tip

canonical :: WordMap v -> Maybe (Node v)
canonical (WordMap (Path _ 0 _)  Nothing) = Nothing
canonical (WordMap (Path k _ ns) Nothing) = Just (unplugPath k 0 (length ns) ns)
canonical (WordMap (Path k _ ns) (Just v)) = Just (plugPath k 0 (length ns) (Tip k v) ns)

-- O(1) plug a child node directly into an open parent node
-- carefully retains identity in case we plug what is already there back in
plug :: Key -> Node v -> Node v -> Node v
plug k z on@(Node ok n m as)
  | wd > 0xf = fork k z ok on
  | m .&. b == 0 = node ok n (m .|. b) (insertSmallArray odm z as)
  | !oz <- indexSmallArray as odm
  , ptrNeq z oz = Node ok n m (updateSmallArray odm z as)
  | otherwise   = on
  where !wd  = unsafeShiftR (xor k ok) n
        !d   = fromIntegral wd
        !b   = unsafeShiftL 1 d
        !odm = index m b
plug k z on@(Full ok n as)
  | wd > 0xf = fork k z ok on
  | !oz <- indexSmallArray as d
  , ptrNeq z oz = Full ok n (update16 d z as)
  | otherwise   = on
  where !wd = unsafeShiftR (xor k ok) n
        !d = fromIntegral wd
plug k z on@(Tip ok _) = fork k z ok on

-- | Given @k@ located under @acc@, @plugPath k i t acc ns@ plugs acc recursively into each of the nodes
-- of @ns@ from @[i..t-1]@ from the bottom up
plugPath :: Key -> Int -> Int -> Node v -> SmallArray (Node v) -> Node v
plugPath !k !i !t !acc !ns
  | i < t     = plugPath k (i+1) t (plug k acc (indexSmallArray ns i)) ns
  | otherwise = acc

-- this recurses into @plugPath@ deliberately.
unplugPath :: Key -> Int -> Int -> SmallArray (Node v) -> Node v
unplugPath !k !i !t !ns = plugPath k (i+1) t (unplug k (indexSmallArray ns i)) ns

unI# :: Int -> Int#
unI# (I# i) = i

-- create a 1-hole context at key k, destroying any previous contents of that position.
path :: Key -> WordMap v -> Path v
path k0 (WordMap p0@(Path ok0 m0 ns0@(SmallArray ns0#)) mv0)
  | k0 == ok0 = p0 -- keys match, easy money
  | m0 == 0 = case mv0 of
    Nothing -> Path k0 0 mempty
    Just v
      | n0 <- level (xor ok0 k0), aok <- unsafeShiftR n0 2
      -> Path k0 (unsafeShiftL 1 aok) $ runST (newSmallArray 1 (Tip ok0 v) >>= unsafeFreezeSmallArray)
  | n0 <- level (xor ok0 k0)
  , aok <- unsafeShiftR n0 2
  , kept <- m0 .&. unsafeShiftL 0xfffe aok
  , nkept@(I# nkept#) <- popCount kept -- 0 -- max (popCount kept - 1) 0
  , !top@(I# top#) <- length ns0 - nkept
  , !root <- (case mv0 of
      Just v -> plugPath ok0 0 top (Tip ok0 v) ns0
      Nothing -> unplugPath ok0 0 top ns0)
  = runST $ primitive $ \s -> case go k0 nkept# root s of
    (# s', ms, m# #) -> case copySmallArray# ns0# top# ms (sizeofSmallMutableArray# ms -# nkept#) nkept# s' of -- we're copying nkept
      s'' -> case unsafeFreezeSmallArray# ms s'' of
        (# s''', spine #) -> (# s''', Path k0 (kept .|. W16# m#) (SmallArray spine) #)
  where
    deep :: Key -> Int# -> SmallArray# (Node v) -> Int# -> Node v -> Int# -> State# s ->
      (# State# s, SmallMutableArray# s (Node v), Word# #)
    deep k h# as d# on n# s = case indexSmallArray# as d# of
      (# on' #) -> case go k (h# +# 1#) on' s of
        (# s', ms, m# #) -> case writeSmallArray# ms (sizeofSmallMutableArray# ms -# h# -# 1#) on s' of
          s'' -> case unsafeShiftL 1 (unsafeShiftR (I# n#) 2) .|. W16# m# of
            W16# m'# -> (# s'', ms, m'# #)

    shallow :: Int# -> Node v -> Int# -> State# s ->
      (# State# s, SmallMutableArray# s (Node v), Word# #)
    shallow h# on n# s = case newSmallArray# (h# +# 1#) on s of
      (# s', ms #) -> case unsafeShiftL 1 (unsafeShiftR (I# n#) 2) of
          W16# m# -> (# s', ms, m# #)

    go :: Key -> Int# -> Node v -> State# s -> (# State# s, SmallMutableArray# s (Node v), Word# #)
    go k h# on@(Full ok n@(I# n#) (SmallArray as)) s
      | wd > 0xf  = shallow h# on (unI# (level okk)) s -- we're a sibling of what we recursed into       -- [Displaced Full]
      | otherwise = deep k h# as (unI# (fromIntegral wd)) on n# s                                        -- Parent Full : ..
      where !okk = xor k ok
            !wd = unsafeShiftR okk n
    go k h# on@(Node ok n@(I# n#) m (SmallArray as)) s
      | wd > 0xf = shallow h# on (unI# (level okk)) s                                                    -- [Displaced Node]
      | !b <- unsafeShiftL 1 (fromIntegral wd), m .&. b /= 0 = deep k h# as (unI# (index m b)) on n# s   -- Parent Node : ..
      | otherwise = shallow h# on n# s                                                                   -- [Node]
      where !okk = xor k ok
            !wd = unsafeShiftR okk n
    go k h# on@(Tip ok _) s 
      | k == ok = case newSmallArray# h# (error "hit") s of (# s', ms #) -> (# s', ms, int2Word# 0# #)
      | otherwise = shallow h# on (unI# (level (xor k ok))) s -- [Displaced Tip]

insert :: Key -> v -> WordMap v -> WordMap v
insert k v wm@(WordMap (Path ok _ _) mv)
  | k == ok, Just ov <- mv, ptrEq v ov = wm
  | otherwise = WordMap (path k wm) (Just v)

delete :: Key -> WordMap v -> WordMap v
delete k m = WordMap (path k m) Nothing

--------------------------------------------------------------------------------
-- * Instances
--------------------------------------------------------------------------------

type instance Index (WordMap a) = Key
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
  imap f (Full k n as) = Full k n (fmap (imap f) as)

instance Foldable WordMap where
  foldMap f wm = foldMap (foldMap f) (canonical wm)
  null (WordMap (Path _ 0 _) Nothing) = True
  null _ = False

instance FoldableWithIndex Word64 WordMap where
  ifoldMap f wm = foldMap (ifoldMap f) (canonical wm)

instance FoldableWithIndex Word64 Node where
  ifoldMap f (Node _ _ _ as) = foldMap (ifoldMap f) as
  ifoldMap f (Tip k v) = f k v
  ifoldMap f (Full _ _ as) = foldMap (ifoldMap f) as

instance Eq v => Eq (WordMap v) where
  as == bs = Exts.toList as == Exts.toList bs

instance Ord v => Ord (WordMap v) where
  compare as bs = compare (Exts.toList as) (Exts.toList bs)

-- TODO: Traversable, TraversableWithIndex Word64 WordMap

instance IsList (WordMap v) where
  type Item (WordMap v) = (Word64, v)

  toList = ifoldr (\i a r -> (i, a): r) []
  {-# INLINE toList #-}

  fromList xs = foldl' (\r (k,v) -> insert k v r) empty xs
  {-# INLINE fromList #-}

  fromListN _ = fromList
  {-# INLINE fromListN #-}

{-
two :: WordMap Word64
two = WordMap (Path 2 1 (fromList [Tip 1 1])) (Just 2)

three :: WordMap Word64
three = WordMap (Path 3 1 (fromList [Node 0 0 6 (fromList [Tip 1 1, Tip 2 2])])) (Just 3)
-}

-- insert 1 1 (insert 100 100 (insert 203 203 (insert 2 2 (insert 1 1 empty))))
--
-- focused on 1 1
-- WordMap (Path 1 3 (fromList [Tip 1 1,Node 0 0 6 (fromList [Tip 1 1,Tip 2 2]),Node 0 4 4161 (fromList [Node 0 0 6 (fromList [Tip 1 1,Tip 2 2]),Tip 100 100,Tip 203 203])])) (Just 1)

-- WordMap (Path 1 3 (fromList [Tip 1 1,Node 0 0 6 (fromList [Tip 1 1,Tip 2 2]),Node 0 4 4161 (fromList [Node 0 0 6 (fromList [Tip 1 1,Tip 2 2]),Tip 100 100,Tip 203 203])])) (Just 1)
