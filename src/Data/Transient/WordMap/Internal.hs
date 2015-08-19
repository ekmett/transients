{-# LANGUAGE CPP #-}
{-# LANGUAGE Unsafe #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
-- {-# OPTIONS_GHC -fobject-code -fno-full-laziness -fno-cse #-}
{-# OPTIONS_GHC -ddump-simpl -dsuppress-all #-}
{-# OPTIONS_HADDOCK not-home #-}

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
module Data.Transient.WordMap.Internal where

import Control.Applicative hiding (empty)
import Control.DeepSeq
import Control.Lens hiding (index, deep)
import Control.Monad
import Control.Monad.ST hiding (runST)
import Control.Monad.Primitive
import Data.Bits
import Data.Foldable (fold)
import Data.Primitive.MutVar
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
ptrEq x y = isTrue# (Exts.reallyUnsafePtrEquality# x y)
{-# INLINEABLE ptrEq #-}

ptrNeq :: a -> a -> Bool
ptrNeq x y = isTrue# (Exts.reallyUnsafePtrEquality# x y `xorI#` 1#)
{-# INLINEABLE ptrNeq #-}

index :: Word16 -> Word16 -> Int
index m b = popCount (m .&. (b-1))
{-# INLINE index #-}

-- | Note: @level 0@ will return a negative shift, so don't use it
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
-- * WordMaps
--------------------------------------------------------------------------------

data Node a
  = Full {-# UNPACK #-} !Key {-# UNPACK #-} !Offset !(SmallArray (Node a))
  | Node {-# UNPACK #-} !Key {-# UNPACK #-} !Offset {-# UNPACK #-} !Mask !(SmallArray (Node a))
  | Tip  {-# UNPACK #-} !Key a
  deriving (Functor,Foldable,Show)

data WordMap a = WordMap
  { fingerKey   :: {-# UNPACK #-} !Key
  , fingerMask  :: {-# UNPACK #-} !Mask
  , fingerValue :: !(Maybe a)
  , fingerPath  :: {-# UNPACK #-} !(SmallArray (Node a))
  } deriving (Functor,Show)

data TNode s a
  = TFull {-# UNPACK #-} !Key {-# UNPACK #-} !Offset !(SmallMutableArray s (TNode s a))
  | TNode {-# UNPACK #-} !Key {-# UNPACK #-} !Offset {-# UNPACK #-} !Mask !(SmallMutableArray s (TNode s a))
  | TTip  {-# UNPACK #-} !Key a

-- | This is a transient WordMap with a clojure-like API
data TWordMap s a = TWordMap
  { transientFingerKey  :: {-# UNPACK #-} !Key
  , transientFingerMask :: {-# UNPACK #-} !Mask
  , transientFingerValue :: !(Maybe a)
  , transientFingerPath :: {-# UNPACK #-} !(SmallMutableArray s (TNode s a))
  }

persisted :: (forall s. TWordMap s a) -> WordMap a
persisted = unsafeCoerce

unsafePersistentTNode :: TNode s a -> Node a
unsafePersistentTNode = unsafeCoerce

unsafePersistent :: TWordMap s a -> WordMap a
unsafePersistent = unsafeCoerce
{-# INLINE unsafePersistent #-}

-- | This is a mutable WordMap with a classic Haskell mutable container-style API
--
-- On the plus side, this API means you don't need to carefully avoid reusing a transient
-- On the minus side, you have an extra reference to track.
newtype MWordMap s a = MWordMap { runMWordMap :: MutVar s (TWordMap s a) }

thaw :: PrimMonad m => WordMap a -> m (MWordMap (PrimState m) a)
thaw m = MWordMap <$> newMutVar (transient m)

freeze :: PrimMonad m => MWordMap (PrimState m) a -> m (WordMap a)
freeze (MWordMap r) = do
  x <- readMutVar r
  persistent x

--------------------------------------------------------------------------------
-- * Transient WordMaps
--------------------------------------------------------------------------------

-- | O(1) worst-case conversion from an immutable structure to a mutable one
transient :: WordMap a -> TWordMap s a
transient = unsafeCoerce
{-# INLINE transient #-}

-- | O(1) amortized conversion from a mutable structure to an immutable one
persistent :: PrimMonad m => TWordMap (PrimState m) a -> m (WordMap a)
persistent r@(TWordMap _ _ _ ns0) = primToPrim $ do
    go ns0
    return (unsafePersistent r)
  where
    go :: SmallMutableArray s (TNode s a) -> ST s ()
    go ns = unsafeCheckSmallMutableArray ns >>= \case
      True  -> walk ns (sizeOfSmallMutableArray ns - 1)
      False -> return ()
    walk :: SmallMutableArray s (TNode s a) -> Int -> ST s ()
    walk ns !i
      | i >= 0 = readSmallArray ns i >>= \case
        TNode _ _ _ as -> do go as; walk ns (i - 1)
        TFull _ _ as   -> do go as; walk ns (i - 1)
        _              -> return ()
      | otherwise = return ()
{-# NOINLINE persistent #-}

empty :: WordMap a
empty = persisted emptyT
{-# NOINLINE empty #-}

emptySmallMutableArray :: SmallMutableArray s a
emptySmallMutableArray = runST $ unsafeCoerce <$> newSmallArray 0 undefined
{-# NOINLINE emptySmallMutableArray #-}

emptyT :: TWordMap s a
emptyT = TWordMap 0 0 Nothing emptySmallMutableArray
{-# INLINE emptyT #-}

emptyM :: PrimMonad m => m (MWordMap (PrimState m) a)
emptyM = thaw empty
{-# INLINE emptyM #-}

-- | Build a singleton WordMap
singleton :: Key -> a -> WordMap a
singleton k v = WordMap k 0 (Just v) mempty
{-# INLINE singleton #-}

singletonT :: Key -> a -> TWordMap s a
singletonT k v = TWordMap k 0 (Just v) emptySmallMutableArray
{-# INLINE singletonT #-}

singletonM :: PrimMonad m => Key -> a -> m (MWordMap (PrimState m) a)
singletonM k v = thaw (singleton k v)

lookup :: Key -> WordMap a -> Maybe a
lookup k m = runST (lookupT k (transient m))
{-# INLINEABLE lookup #-}

lookupM :: PrimMonad m => Key -> MWordMap (PrimState m) a -> m (Maybe a)
lookupM k0 (MWordMap m) = do
  x <- readMutVar m
  lookupT k0 x
{-# INLINE lookupM #-}

lookupT :: PrimMonad m => Key -> TWordMap (PrimState m) a -> m (Maybe a)
lookupT k0 (TWordMap ok m mv mns)
  | k0 == ok = return mv
  | b <- apogee k0 ok = if
    | m .&. b == 0 -> return Nothing
    | otherwise    -> do
      x <- readSmallArray mns (index m b)
      primToPrim (lookupTNode k0 x)
{-# INLINEABLE lookupT #-}

lookupTNode :: Key -> TNode s a -> ST s (Maybe a)
lookupTNode !k (TFull ok o a)
  | z > 0xf   = return Nothing
  | otherwise = do
    x <- readSmallArray a (fromIntegral z)
    lookupTNode k x
  where
    z = unsafeShiftR (xor k ok) o
lookupTNode k (TNode ok o m a)
  | z > 0xf      = return Nothing
  | m .&. b == 0 = return Nothing
  | otherwise = do
    x <- readSmallArray a (index m b)
    lookupTNode k x
  where
    z = unsafeShiftR (xor k ok) o
    b = unsafeShiftL 1 (fromIntegral z)
lookupTNode k (TTip ok ov)
  | k == ok   = return (Just ov)
  | otherwise = return (Nothing)

-- | Modify an immutable structure with mutable operations.
--
-- @modify f wm@ passed @f@ a "persisted" transient that may be reused.
modify :: (forall s. TWordMap s a -> ST s (TWordMap s b)) -> WordMap a -> WordMap b
modify f wm = runST $ do
  mwm <- f (transient wm)
  persistent mwm
{-# INLINE modify #-}

-- | Modify a mutable wordmap with a transient operation.
modifyM :: PrimMonad m => (TWordMap (PrimState m) a -> m (TWordMap (PrimState m) a)) -> MWordMap (PrimState m) a -> m ()
modifyM f (MWordMap r) = do
  t <- readMutVar r
  t' <- f t
  writeMutVar r t'
{-# INLINE modifyM #-}

{-# RULES "persistent/transient" forall m. persistent (unsafeCoerce m) = return m #-}

-- | Query a transient structure with queries designed for an immutable structure.
--
-- This does _not_ destroy the transient, although, it does mean subsequent actions need to copy-on-write from scratch.
--
-- After @query f wm@, @wm@ is considered persisted and may be reused.
query :: PrimMonad m => (WordMap a -> r) -> TWordMap (PrimState m) a -> m r
query f t = f <$> persistent t
{-# INLINE query #-}

-- | Query a mutable structure with queries designed for an immutable structure.
queryM :: PrimMonad m => (WordMap a -> r) -> MWordMap (PrimState m) a -> m r
queryM f (MWordMap m) = do
  t <- readMutVar m 
  query f t
{-# INLINE queryM #-}

--------------------------------------------------------------------------------
-- * Construction
--------------------------------------------------------------------------------

-- @
-- unsafeFreezeSmallArray# :: Hint s
-- warm :: Hint s
-- @
--
-- invariant: everything below a given position in a tree must be at least this persisted
type Hint s = forall x. SmallMutableArray# s x -> State# s -> State# s

warm :: Hint s
warm _ s = s
{-# INLINE warm #-}

cold :: Hint s
cold m s = case unsafeFreezeSmallArray# m s of (# s', _ #) -> s'
{-# NOINLINE cold #-}

apply :: PrimMonad m => Hint (PrimState m) -> SmallMutableArray (PrimState m) a -> m ()
apply hint (SmallMutableArray m) = primitive_ (hint m)
{-# INLINE apply #-}

insertSmallArray :: Hint s -> SmallMutableArray s a -> Int -> a -> ST s (SmallMutableArray s a)
insertSmallArray hint i k a = do
  let n = sizeOfSmallMutableArray i
  o <- newSmallArray (n + 1) a
  copySmallMutableArray o 0 i 0 k -- backwards `primitive` convention
  copySmallMutableArray o (k+1) i k (n-k) -- backwards `primitive` convention
  apply hint o
  return o
{-# INLINEABLE insertSmallArray #-}

deleteSmallArray :: Hint s -> SmallMutableArray s a -> Int -> ST s (SmallMutableArray s a)
deleteSmallArray hint i k = do
  let n = sizeOfSmallMutableArray i
  o <- newSmallArray (n - 1) undefined
  copySmallMutableArray o 0 i 0 k -- backwards `primitive` convention
  copySmallMutableArray o k i (k+1) (n-k-1) -- backwards `primitive` convention
  apply hint o
  return o
{-# INLINEABLE deleteSmallArray #-}

node :: Key -> Offset -> Mask -> SmallMutableArray s (TNode s a) -> TNode s a
node k o 0xffff a = TFull k o a
node k o m a      = TNode k o m a
{-# INLINE node #-}

fork :: Hint s -> Key -> TNode s a -> Key -> TNode s a -> ST s (TNode s a)
fork hint k n ok on = do
  arr <- newSmallArray 2 n
  writeSmallArray arr (fromEnum (k < ok)) on
  let o = level (xor k ok)
  apply hint arr
  return $! TNode (k .&. unsafeShiftL 0xfffffffffffffff0 o) o (mask k o .|. mask ok o) arr

-- O(1) remove the _entire_ branch containing a given node from this tree, in situ
unplug :: Hint s -> Key -> TNode s a -> ST s (TNode s a)
unplug hint k on@(TFull ok n as)
  | wd >= 0xf = return on
  | d <- fromIntegral wd = TNode ok n (complement (unsafeShiftL 1 d)) <$> deleteSmallArray hint as d
  where !wd = unsafeShiftR (xor k ok) n
unplug hint !k on@(TNode ok n m as)
  | wd >= 0xf = return on
  | !b <- unsafeShiftL 1 (fromIntegral wd), m .&. b /= 0, p <- index m b =
    if sizeOfSmallMutableArray as == 2
     then readSmallArray as (1-p) -- keep the other node
     else TNode ok n (m .&. complement b) <$> deleteSmallArray hint as p
  | otherwise = return on
  where !wd = unsafeShiftR (xor k ok) n
unplug _ _ on = return on

canonical :: WordMap a -> Maybe (Node a)
canonical wm = runST $ case transient wm of
  TWordMap _ 0 Nothing _ -> return Nothing
  TWordMap k _ mv ns -> Just . unsafePersistentTNode <$> replugPath cold k 0 (sizeOfSmallMutableArray ns) mv ns

-- O(1) plug a child node directly into an open parent node
-- carefully retains identity in case we plug what is already there back in
plug :: Hint s -> Key -> TNode s a -> TNode s a -> ST s (TNode s a)
plug hint k z on@(TNode ok n m as)
  | wd > 0xf = fork hint k z ok on
  | otherwise = do
    let d   = fromIntegral wd
        b   = unsafeShiftL 1 d
        odm = index m b
    if m .&. b == 0
      then node ok n (m .|. b) <$> insertSmallArray hint as odm z
      else unsafeCheckSmallMutableArray as >>= \case
        True -> do -- really mutable, mutate in place
          writeSmallArray as odm z
          apply hint as -- we may be freezing as we go, apply the hint
          return on
        False -> do -- this is a persisted node
          !oz <- readSmallArray as odm
          if ptrEq oz z
            then return on -- but we arent changing it
            else do -- here we are, and we need to copy on write
              bs <- cloneSmallMutableArray as 0 odm
              writeSmallArray bs odm z
              apply hint bs
              return (TNode ok n m bs)
  where wd = unsafeShiftR (xor k ok) n
plug hint k z on@(TFull ok n as)
  | wd > 0xf = fork hint k z ok on
  | otherwise = do
    let d = fromIntegral wd
    unsafeCheckSmallMutableArray as >>= \case
      True -> do
        writeSmallArray as d z
        apply hint as
        return on
      False -> do
        !oz <- readSmallArray as d
        if ptrEq oz z
          then return on
          else do
            bs <- cloneSmallMutableArray as 0 16
            writeSmallArray bs d z
            apply hint bs
            return (TFull ok n bs)
  where wd = unsafeShiftR (xor k ok) n
plug hint k z on@(TTip ok _) = fork hint k z ok on

-- | Given @k@ located under @acc@, @plugPath k i t acc ns@ plugs acc recursively into each of the nodes
-- of @ns@ from @[i..t-1]@ from the bottom up
plugPath :: Hint s -> Key -> Int -> Int -> TNode s a -> SmallMutableArray s (TNode s a) -> ST s (TNode s a)
plugPath hint !k !i !t !acc !ns
  | i < t     = do
    x <- readSmallArray ns i
    y <- plug hint k acc x
    plugPath hint k (i+1) t y ns
  | otherwise = return acc

-- this recurses into @plugPath@ deliberately.
unplugPath :: Hint s -> Key -> Int -> Int -> SmallMutableArray s (TNode s a) -> ST s (TNode s a)
unplugPath hint k i t ns = do
  x <- readSmallArray ns i
  y <- unplug hint k x
  plugPath hint k (i+1) t y ns

replugPath :: PrimMonad m => Hint (PrimState m) -> Key -> Int -> Int -> Maybe v -> SmallMutableArray (PrimState m) (TNode (PrimState m) v) -> m (TNode (PrimState m) v)
replugPath hint k i t (Just v) ns = primToPrim $ plugPath hint k i t (TTip k v) ns
replugPath hint k i t Nothing ns  = primToPrim $ unplugPath hint k i t ns

unI# :: Int -> Int#
unI# (I# i) = i

-- | O(1) This function enables us to GC the items that lie on the path to the finger.
--
-- Normally we only do this lazily as the finger moves out of a given area, but if you have
-- particularly burdensome items for the garbage collector it may be worth paying this price
-- to explicitly allow them to go free.
trimT :: PrimMonad m => TWordMap (PrimState m) a -> m (TWordMap (PrimState m) a)
trimT wm@(TWordMap _ 0 _ _)    = return wm
trimT wm0@(TWordMap k0 m mv ns) = primToPrim $ unsafeCheckSmallMutableArray ns >>= \case
    True -> go k0 ns ns (n-1) wm0
    False -> do
      ns' <- newSmallArray n undefined
      go k0 ns' ns (n-1) (TWordMap k0 m mv ns')
  where
    n = sizeOfSmallMutableArray ns
    go :: Key -> SmallMutableArray s (TNode s a) -> SmallMutableArray s (TNode s a) -> Int -> TWordMap s a -> ST s (TWordMap s a)
    go k dst src i wm
      | i >= 0 = do
        x <- readSmallArray src i
        y <- unplug warm k x
        writeSmallArray dst i y
        go k dst src (i - 1) wm
      | otherwise = return wm

-- | O(1) This function enables us to GC the items that lie on the path to the finger.
--
-- Normally we only do this lazily as the finger moves out of a given area, but if you
-- have particularly burdensome items for the garbage collector it may be worth paying this price.
-- to explicitly allow them to go free.
trimM :: PrimMonad m => MWordMap (PrimState m) a -> m ()
trimM = modifyM trimT
{-# INLINE trimM #-}

-- | O(1) This function enables us to GC the items that lie on the path to the finger.
--
-- Normally we only do this lazily as the finger moves out of a given area, but if you
-- have particularly burdensome items for the garbage collector it may be worth paying this price.
-- to explicitly allow them to go free.
trim :: WordMap a -> WordMap a
trim = modify trimT
{-# INLINE trim #-}

focusWithHint :: PrimMonad m => Hint (PrimState m) -> Key -> TWordMap (PrimState m) a -> m (TWordMap (PrimState m) a)
focusWithHint hint k0 wm0@(TWordMap ok0 m0 mv0 ns0@(SmallMutableArray ns0#))
  | k0 == ok0 = return wm0 -- keys match, easy money
  | m0 == 0 = case mv0 of
    Nothing -> return (TWordMap k0 0 Nothing emptySmallMutableArray)
    Just v  -> do
      ns <- newSmallArray 1 (TTip ok0 v)
      apply hint ns
      return $! TWordMap k0 (unsafeShiftL 1 (unsafeShiftR (level (xor ok0 k0)) 2)) Nothing ns
  | kept <- m0 .&. unsafeShiftL 0xfffe (unsafeShiftR (level (xor ok0 k0)) 2)
  , nkept@(I# nkept#) <- popCount kept
  , top@(I# top#) <- sizeOfSmallMutableArray ns0 - nkept
  = do
    root <- replugPath hint ok0 0 top mv0 ns0
    primitive $ \s -> case go k0 nkept# root s of
      (# s', ms, m#, omv #) -> case copySmallMutableArray# ns0# top# ms (sizeofSmallMutableArray# ms -# nkept#) nkept# s' of -- we're copying nkept
        s'' -> case hint ms s'' of
          s''' -> (# s''', TWordMap k0 (kept .|. W16# m#) omv (SmallMutableArray ms) #)
  where
    deep :: Key -> Int# -> SmallMutableArray# s (TNode s a) -> Int# -> TNode s a -> Int# -> State# s ->
      (# State# s, SmallMutableArray# s (TNode s a), Word#, Maybe a #)
    deep k h# as d# on n# s = case readSmallArray# as d# s of
      (# s', on' #) -> case go k (h# +# 1#) on' s' of
        (# s'', ms, m#, mv #) -> case writeSmallArray# ms (sizeofSmallMutableArray# ms -# h# -# 1#) on s'' of
          s''' -> case unsafeShiftL 1 (unsafeShiftR (I# n#) 2) .|. W16# m# of
            W16# m'# -> (# s''', ms, m'#, mv #)

    shallow :: Int# -> TNode s a -> Int# -> Maybe a -> State# s ->
      (# State# s, SmallMutableArray# s (TNode s a), Word#, Maybe a #)
    shallow h# on n# mv s = case newSmallArray# (h# +# 1#) on s of
      (# s', ms #) -> case unsafeShiftL 1 (unsafeShiftR (I# n#) 2) of
        W16# m# -> (# s', ms, m#, mv #)

    go :: Key -> Int# -> TNode s a -> State# s -> (# State# s, SmallMutableArray# s (TNode s a), Word#, Maybe a #)
    go k h# on@(TFull ok n@(I# n#) (SmallMutableArray as)) s
      | wd > 0xf  = shallow h# on (unI# (level okk)) Nothing s -- we're a sibling of what we recursed into  -- [Displaced TFull]
      | otherwise = deep k h# as (unI# (fromIntegral wd)) on n# s                                           -- Parent TFull : ..
      where !okk = xor k ok
            !wd = unsafeShiftR okk n
    go k h# on@(TNode ok n@(I# n#) m (SmallMutableArray as)) s
      | wd > 0xf = shallow h# on (unI# (level okk)) Nothing s                                            -- [Displaced TNode]
      | !b <- unsafeShiftL 1 (fromIntegral wd), m .&. b /= 0 = deep k h# as (unI# (index m b)) on n# s   -- Parent TNode : ..
      | otherwise = shallow h# on n# Nothing s                                                           -- [TNode]
      where !okk = xor k ok
            !wd = unsafeShiftR okk n
    go k h# on@(TTip ok v) s
      | k == ok = case newSmallArray# h# undefined s of (# s', ms #) -> (# s', ms, int2Word# 0#, Just v #)
      | otherwise = shallow h# on (unI# (level (xor k ok))) Nothing s -- [Displaced TTip]

-- | This changes the location of the focus in a transient map. Operations near the focus are considerably cheaper.
--
-- @focusT k wm@ invalidates any unpersisted transient @wm@ it is passed
focusT :: PrimMonad m => Key -> TWordMap (PrimState m) a -> m (TWordMap (PrimState m) a)
focusT = focusWithHint warm
{-# INLINE focusT #-}

-- | This changes the location of the focus in a mutable map. Operations near the focus are considerably cheaper.
focusM :: PrimMonad m => Key -> MWordMap (PrimState m) a -> m ()
focusM k = modifyM (focusT k)
{-# INLINE focusM #-}

-- | This changes the location of the focus in an immutable map. Operations near the focus are considerably cheaper.
focus :: Key -> WordMap a -> WordMap a
focus k wm = modify (focusWithHint cold k) wm
{-# INLINE focus #-}

insertWithHint :: PrimMonad m => Hint (PrimState m) -> Key -> a -> TWordMap (PrimState m) a -> m (TWordMap (PrimState m) a)
insertWithHint hint k v wm@(TWordMap ok _ mv _)
  | k == ok, Just ov <- mv, ptrEq v ov = return wm
  | otherwise = do
    wm' <- focusWithHint hint k wm
    return $! wm' { transientFingerValue = Just v }
{-# INLINE insertWithHint #-}

-- | Transient insert.
-- 
-- @insertT k v wm@ invalidates any unpersisted transient @wm@ it is passed
insertT :: PrimMonad m => Key -> a -> TWordMap (PrimState m) a -> m (TWordMap (PrimState m) a)
insertT k v wm = insertWithHint warm k v wm
{-# INLINE insertT #-}

-- | Mutable insert.
insertM :: PrimMonad m => Key -> a -> MWordMap (PrimState m) a -> m ()
insertM k v mwm = modifyM (insertT k v) mwm
{-# INLINE insertM #-}

-- | Immutable insert.
insert :: Key -> a -> WordMap a -> WordMap a
insert k v wm = modify (insertWithHint cold k v) wm
{-# INLINE insert #-}

deleteWithHint :: PrimMonad m => Hint (PrimState m) -> Key -> TWordMap (PrimState m) a -> m (TWordMap (PrimState m) a)
deleteWithHint hint k wm = do
  wm' <- focusWithHint hint k wm
  case transientFingerValue wm' of
    Nothing -> return wm'
    _       -> return $! wm' { transientFingerValue = Nothing }
{-# INLINE deleteWithHint #-}

-- | Transient delete. @deleteT k v wm@ invalidates any unpersisted transient it is passed.
deleteT :: PrimMonad m => Key -> TWordMap (PrimState m) a -> m (TWordMap (PrimState m) a)
deleteT k wm = deleteWithHint warm k wm
{-# INLINE deleteT #-}

-- | Mutable delete.
deleteM :: PrimMonad m => Key -> MWordMap (PrimState m) a -> m ()
deleteM k wm = modifyM (deleteT k) wm
{-# INLINE deleteM #-}

-- | Immutable delete.
delete :: Key -> WordMap a -> WordMap a
delete k wm = modify (deleteWithHint cold k) wm
{-# INLINE delete #-}

--------------------------------------------------------------------------------
-- * Instances
--------------------------------------------------------------------------------

instance IsList (WordMap a) where
  type Item (WordMap a) = (Word64, a)

  toList = ifoldr (\i a r -> (i, a): r) []
  {-# INLINE toList #-}

  fromList xs = runST $ do
     o <- foldM (\r (k,v) -> insertT k v r) emptyT xs
     persistent o
  {-# INLINE fromList #-}

  fromListN _ = fromList
  {-# INLINE fromListN #-}

-- stuff to eventually clean up and reintroduce

type instance Index (WordMap a) = Key
type instance IxValue (WordMap a) = a

instance At (WordMap a) where
  at k f wm = let c = focus k wm in f (lookup k wm) <&> \mv' -> c { fingerValue = mv' }
  {-# INLINE at #-}

instance Ixed (WordMap a) where
  ix k f wm = case lookup k wm of
    Nothing -> pure wm
    Just v  -> let c = focus k wm in f v <&> \v' -> c { fingerValue = Just v' }

instance NFData a => NFData (Node a) where
  rnf (Full _ _ a)   = rnf a
  rnf (Node _ _ _ a) = rnf a
  rnf (Tip _ v)      = rnf v

instance NFData a => NFData (WordMap a) where
  rnf (WordMap _ _ mv as) = rnf mv `seq` rnf as

instance AsEmpty (WordMap a) where
  _Empty = prism (const empty) $ \s -> case s of
    WordMap _ 0 Nothing _ -> Right ()
    t -> Left t

instance AsEmpty (TWordMap s a) where
  _Empty = prism (const emptyT) $ \s -> case s of
    TWordMap _ 0 Nothing _ -> Right ()
    t -> Left t

instance Eq (MWordMap s a) where
  MWordMap m == MWordMap n = m == n

instance FunctorWithIndex Word64 WordMap where
  imap f (WordMap k n mv as) = WordMap k n (fmap (f k) mv) (fmap (imap f) as)

instance FunctorWithIndex Word64 Node where
  imap f (Node k n m as) = Node k n m (fmap (imap f) as)
  imap f (Tip k v)       = Tip k (f k v)
  imap f (Full k n as)   = Full k n (fmap (imap f) as)

instance Foldable WordMap where
  fold wm = foldMap fold (canonical wm)
  foldMap f wm = foldMap (foldMap f) (canonical wm)
  null (WordMap _ 0 Nothing _) = True
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
-- TODO: instance Eq (TWordMap s)
