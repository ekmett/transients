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
{-# LANGUAGE RoleAnnotations #-}
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
module Data.Transient.WordMap
{-
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
  ) -} where

import Control.Applicative hiding (empty)
import Control.DeepSeq
import Control.Lens hiding (index, deep)
import Control.Monad
import Control.Monad.ST hiding (runST)
import Control.Monad.Primitive
import Data.Bits
import Data.Foldable
import Data.Monoid
import Data.Primitive.MutVar
import Data.Transient.Primitive.Exts
import Data.Transient.Primitive.SmallArray
import Data.Transient.Primitive.Unsafe
import Data.Word
import qualified GHC.Exts as Exts
import Prelude hiding (lookup, length, foldr)
import GHC.Exts as Exts
import GHC.ST
import GHC.Word
import Unsafe.Coerce

type Key = Word64
type Mask = Word16
type Offset = Int

--------------------------------------------------------------------------------
-- * Utilities
--------------------------------------------------------------------------------

ptrEq :: a -> a -> Bool
ptrEq x y = isTrue# (Exts.reallyUnsafePtrEquality# x y Exts.==# 1#)
-- ptrEq _ _ = False
{-# INLINEABLE ptrEq #-}

ptrNeq :: a -> a -> Bool
ptrNeq x y = isTrue# (Exts.reallyUnsafePtrEquality# x y Exts./=# 1#)
-- ptrNeq _ _ = True
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
-- * Nodes
--------------------------------------------------------------------------------

data FrozenNode v
  = FrozenFull {-# UNPACK #-} !Key {-# UNPACK #-} !Offset !(SmallArray (FrozenNode v))
  | FrozenNode {-# UNPACK #-} !Key {-# UNPACK #-} !Offset {-# UNPACK #-} !Mask !(SmallArray (FrozenNode v))
  | FrozenTip  {-# UNPACK #-} !Key v
  deriving (Functor,Foldable,Traversable,Show)

type role FrozenNode representational

-- NB: FrozenNode v must be representationally equivalent to Node s v, modulo the use of the free list.
coerceNode :: FrozenNode v -> Node s v
coerceNode = unsafeCoerce
{-# INLINE coerceNode #-}

data Node s v 
  = Full {-# UNPACK #-} !Key {-# UNPACK #-} !Offset !(SmallMutableArray s (Node s v))
  | Node {-# UNPACK #-} !Key {-# UNPACK #-} !Offset {-# UNPACK #-} !Mask !(SmallMutableArray s (Node s v))
  | Tip  {-# UNPACK #-} !Key v

type role Node nominal representational

--------------------------------------------------------------------------------
-- * WordMaps
--------------------------------------------------------------------------------

data WordMap v = FrozenWordMap {-# UNPACK #-} !Key {-# UNPACK #-} !Mask {-# UNPACK #-} !(SmallArray (FrozenNode v)) !(Maybe v)
  deriving (Functor,Foldable,Traversable,Show)

type role WordMap representational

data Root s v = WordMap {-# UNPACK #-} !Key {-# UNPACK #-} !Mask {-# UNPACK #-} !(SmallMutableArray s (Node s v)) !(Maybe v)

type role Root nominal representational

-- NB: Root v must be representationally equivalent to Node s v, modulo the use of the free list.
coerceRoot :: WordMap v -> Root s v
coerceRoot = unsafeCoerce

newtype TWordMap s v = TWordMap { getTWordMap :: MutVar s (Root s v) }

type role TWordMap nominal representational

--------------------------------------------------------------------------------
-- * Transient WordMaps
--------------------------------------------------------------------------------

thaw :: PrimMonad m => WordMap v -> m (TWordMap (PrimState m) v )
thaw m = TWordMap <$> newMutVar (unsafeCoerce m)

unsafeFreeze :: PrimMonad m => TWordMap (PrimState m) v -> m (WordMap v)
unsafeFreeze (TWordMap m) = primToPrim $ do
    r@(WordMap _ _ ns _) <- readMutVar m
    go ns 
    return (unsafeCoerce r)
  where
    go :: SmallMutableArray s (Node s a) -> ST s ()
    go ns = unsafeCheckSmallMutableArray ns >>= \case
      True  -> walk ns (sizeOfSmallMutableArray ns - 1)
      False -> return ()
    walk :: SmallMutableArray s (Node s a) -> Int -> ST s ()
    walk ns !i
      | i >= 0 = readSmallArray ns i >>= \case
        Node _ _ _ as -> do go as; walk ns (i - 1)
        Full _ _ as   -> do go as; walk ns (i - 1)
        _              -> return ()
      | otherwise = return ()

empty :: WordMap v
empty = FrozenWordMap 0 0 mempty Nothing
{-# NOINLINE empty #-}

emptyM :: PrimMonad m => m (TWordMap (PrimState m) v)
emptyM = thaw empty
{-# INLINE emptyM #-}

-- | Build a singleton Node
singleton :: Key -> v -> WordMap v
singleton k v = FrozenWordMap k 0 mempty (Just v)
{-# INLINE singleton #-}

singletonM :: PrimMonad m => Key -> v -> m (TWordMap (PrimState m) v)
singletonM k v = thaw (singleton k v)
{-# INLINE singletonM #-}

lookupM :: PrimMonad m => Key -> TWordMap (PrimState m) v -> m (Maybe v)
lookupM k0 (TWordMap r) = primToPrim $ do
  x <- readMutVar r
  lookupRootM k0 x
{-# INLINEABLE lookupM #-}

lookup :: Key -> WordMap v -> Maybe v
lookup k m = runST (lookupRootM k (coerceRoot m))
{-# INLINEABLE lookup #-}

lookupRootM :: Key -> Root s v -> ST s (Maybe v)
lookupRootM k0 (WordMap ok m mns mv)
  | k0 == ok = return mv
  | b <- apogee k0 ok = if
    | m .&. b == 0 -> return Nothing
    | otherwise    -> do
      x <- readSmallArray mns (index m b)
      lookupNodeM k0 x
{-# INLINEABLE lookupRootM #-}

lookupNodeM :: Key -> Node s v -> ST s (Maybe v)
lookupNodeM !k (Full ok o a)
  | z > 0xf   = return Nothing
  | otherwise = do
    x <- readSmallArray a (fromIntegral z)
    lookupNodeM k x
  where
    z = unsafeShiftR (xor k ok) o
lookupNodeM k (Node ok o m a)
  | z > 0xf      = return Nothing
  | m .&. b == 0 = return Nothing
  | otherwise = do
    x <- readSmallArray a (index m b)
    lookupNodeM k x
  where
    z = unsafeShiftR (xor k ok) o
    b = unsafeShiftL 1 (fromIntegral z)
lookupNodeM k (Tip ok ov)
  | k == ok   = return (Just ov)
  | otherwise = return (Nothing)

--------------------------------------------------------------------------------
-- * Construction
--------------------------------------------------------------------------------

node :: Key -> Offset -> Mask -> SmallMutableArray s (Node s v) -> Node s v
node k o 0xffff a = Full k o a
node k o m a      = Node k o m a
{-# INLINE node #-}

fork :: Key -> Node s v -> Key -> Node s v -> ST s (Node s v)
fork k n ok on = do
  arr <- newSmallArray 2 n
  writeSmallArray arr (fromEnum (k < ok)) on
  let o = level (xor k ok)
  return $! Node (k .&. unsafeShiftL 0xfffffffffffffff0 o) o (mask k o .|. mask ok o) arr

-- O(1) remove the _entire_ branch containing a given node from this tree, in situ
unplug :: Key -> Node s v -> ST s (Node s v)
unplug k on@(Full ok n as)
  | wd >= 0xf = return on
  | d <- fromIntegral wd = Node ok n (complement (unsafeShiftL 1 d)) <$> deleteSmallArray d as
  where !wd = unsafeShiftR (xor k ok) n
unplug !k on@(Node ok n m as)
  | wd >= 0xf = return on
  | !b <- unsafeShiftL 1 (fromIntegral wd), m .&. b /= 0, p <- index m b =
    if sizeOfSmallMutableArray as == 2
     then readSmallArray as (1-p) -- keep the other node
     else Node ok n (m .&. complement b) <$> deleteSmallArray p as
  | otherwise = return on
  where !wd = unsafeShiftR (xor k ok) n
unplug _ on = return on

{-
canonical :: WordMap v -> Maybe (Node v)
canonical (WordMap (Path _ 0 _)  Nothing) = Nothing
canonical (WordMap (Path k _ ns) Nothing) = Just (unplugPath k 0 (length ns) ns)
canonical (WordMap (Path k _ ns) (Just v)) = Just (plugPath k 0 (length ns) (Tip k v) ns)
-}

-- O(1) plug a child node directly into an open parent node
-- carefully retains identity in case we plug what is already there back in
plug :: Key -> Node s v -> Node s v -> ST s (Node s v)
plug k z on@(Node ok n m as)
  | wd > 0xf = fork k z ok on
  | otherwise = do
    let d   = fromIntegral wd
        b   = unsafeShiftL 1 d
        odm = index m b
    if m .&. b == 0
      then node ok n (m .|. b) <$> insertSmallArray odm z as
      else unsafeCheckSmallMutableArray as >>= \case
        True -> do -- really mutable, mutate in place
          writeSmallArray as odm z
          return on
        False -> do -- this is a frozen node
          !oz <- readSmallArray as odm
          if ptrEq oz z
            then return on -- but we arent changing it
            else do -- and we need to copy on write
              bs <- cloneSmallMutableArray as 0 odm 
              writeSmallArray bs odm z
              return (Node ok n m bs)
  where wd = unsafeShiftR (xor k ok) n
plug k z on@(Full ok n as)
  | wd > 0xf = fork k z ok on
  | otherwise = do
    let d = fromIntegral wd
    unsafeCheckSmallMutableArray as >>= \case
      True -> do
        writeSmallArray as d z
        return on
      False -> do
        !oz <- readSmallArray as d
        if ptrEq oz z
          then return on
          else do
            bs <- cloneSmallMutableArray as 0 16
            writeSmallArray bs d z
            return (Full ok n bs)
  where wd = unsafeShiftR (xor k ok) n
plug k z on@(Tip ok _) = fork k z ok on


-- | Given @k@ located under @acc@, @plugPath k i t acc ns@ plugs acc recursively into each of the nodes
-- of @ns@ from @[i..t-1]@ from the bottom up
plugPath :: Key -> Int -> Int -> Node s v -> SmallMutableArray s (Node s v) -> ST s (Node s v)
plugPath !k !i !t !acc !ns
  | i < t     = do
    x <- readSmallArray ns i
    y <- plug k acc x
    plugPath k (i+1) t y ns
  | otherwise = return acc


-- this recurses into @plugPath@ deliberately.
unplugPath :: Key -> Int -> Int -> SmallMutableArray s (Node s v) -> ST s (Node s v)
unplugPath !k !i !t !ns = do
  x <- readSmallArray ns i
  y <- unplug k x
  plugPath k (i+1) t y ns


unI# :: Int -> Int#
unI# (I# i) = i

{-
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
  , nkept@(I# nkept#) <- popCount kept
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

focus :: Key -> WordMap v -> WordMap v
focus k m = WordMap (path k m) (lookup k m)


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

-}

insertSmallArray :: Int -> a -> SmallMutableArray s a -> ST s (SmallMutableArray s a)
insertSmallArray !k a i = do
  let n = sizeOfSmallMutableArray i
  o <- newSmallArray (n + 1) a
  copySmallMutableArray  o 0 i 0 k
  copySmallMutableArray  o (k+1) i k (n-k)
  return o
{-# INLINEABLE insertSmallArray #-}

deleteSmallArray :: Int -> SmallMutableArray s a -> ST s (SmallMutableArray s a)
deleteSmallArray !k i = do
  let n = sizeOfSmallMutableArray i
  o <- newSmallArray (n - 1) undefined
  copySmallMutableArray o 0 i 0 k
  copySmallMutableArray o k i (k+1) (n-k-1)
  return o
{-# INLINEABLE deleteSmallArray #-}

{-

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
-}
