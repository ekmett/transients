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

data Node s a 
  = Full {-# UNPACK #-} !Key {-# UNPACK #-} !Offset !(SmallMutableArray s (Node s a))
  | Node {-# UNPACK #-} !Key {-# UNPACK #-} !Offset {-# UNPACK #-} !Mask !(SmallMutableArray s (Node s a))
  | Tip  {-# UNPACK #-} !Key a

--------------------------------------------------------------------------------
-- * WordMaps
--------------------------------------------------------------------------------

{-
newtype WordMap a = Frozen { thaw :: forall s. TWordMap s a }

frozen :: (forall s. TWordMap s a) -> WordMap a
frozen = Frozen
-}

data FrozenNode a 
  = FrozenFull {-# UNPACK #-} !Key {-# UNPACK #-} !Offset !(SmallArray (FrozenNode a))
  | FrozenNode {-# UNPACK #-} !Key {-# UNPACK #-} !Offset {-# UNPACK #-} !Mask !(SmallArray (FrozenNode a))
  | FrozenTip  {-# UNPACK #-} !Key a
  deriving (Functor,Foldable,Show)

data WordMap a = FrozenWordMap
  { frozenFingerKey :: {-# UNPACK #-} !Key
  , frozenFingerMask :: {-# UNPACK #-} !Mask
  , frozenFingerValue :: !(Maybe a)
  , frozenFingerPath :: {-# UNPACK #-} !(SmallArray (FrozenNode a))
  } deriving (Functor,Show)

frozen :: (forall s. TWordMap s a) -> WordMap a
frozen = unsafeCoerce

thaw :: WordMap a -> TWordMap s a 
thaw = unsafeCoerce

reallyUnsafeFreezeNode :: Node s a -> FrozenNode a
reallyUnsafeFreezeNode = unsafeCoerce

-- | This is a transient WordMap.
data TWordMap s a = WordMap 
  { fingerKey   :: {-# UNPACK #-} !Key
  , fingerMask  :: {-# UNPACK #-} !Mask
  , fingerValue :: !(Maybe a)
  , fingerPath  :: {-# UNPACK #-} !(SmallMutableArray s (Node s a))
  }

--------------------------------------------------------------------------------
-- * Transient WordMaps
--------------------------------------------------------------------------------

reallyUnsafeFreeze :: TWordMap s a -> WordMap a
reallyUnsafeFreeze = unsafeCoerce
{-# INLINE reallyUnsafeFreeze #-}

unsafeFreeze :: PrimMonad m => TWordMap (PrimState m) a -> m (WordMap a)
unsafeFreeze r@(WordMap _ _ _ ns0) = primToPrim $ do
    go ns0 
    return (reallyUnsafeFreeze r)
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

empty :: WordMap a
empty = frozen emptyM
{-# NOINLINE empty #-}

emptySmallMutableArray :: SmallMutableArray s a
emptySmallMutableArray = runST $ unsafeCoerce <$> newSmallArray 0 undefined
{-# NOINLINE emptySmallMutableArray #-}

emptyM :: TWordMap s a
emptyM = WordMap 0 0 Nothing emptySmallMutableArray
{-# INLINE emptyM #-}

-- | Build a singleton Node
singleton :: Key -> a -> WordMap a
singleton k v = frozen (singletonM k v)
{-# INLINE singleton #-}

singletonM :: Key -> a -> TWordMap s a
singletonM k v = WordMap k 0 (Just v) emptySmallMutableArray
{-# INLINE singletonM #-}

lookup :: Key -> WordMap a -> Maybe a
lookup k m = runST (lookupM k (thaw m))
{-# INLINEABLE lookup #-}

lookupM :: PrimMonad m => Key -> TWordMap (PrimState m) a -> m (Maybe a)
lookupM k0 (WordMap ok m mv mns)
  | k0 == ok = return mv
  | b <- apogee k0 ok = if
    | m .&. b == 0 -> return Nothing
    | otherwise    -> do
      x <- readSmallArray mns (index m b)
      primToPrim (lookupNodeM k0 x)
{-# INLINEABLE lookupM #-}

lookupNodeM :: Key -> Node s a -> ST s (Maybe a)
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

-- @
-- unsafeFreezeSmallArray# :: Hint s
-- warm :: Hint s
-- @
--
-- invariant: everything below a given position in a tree must be at least this frozen
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

node :: Key -> Offset -> Mask -> SmallMutableArray s (Node s a) -> Node s a
node k o 0xffff a = Full k o a
node k o m a      = Node k o m a
{-# INLINE node #-}

fork :: Hint s -> Key -> Node s a -> Key -> Node s a -> ST s (Node s a)
fork hint k n ok on = do
  arr <- newSmallArray 2 n
  writeSmallArray arr (fromEnum (k < ok)) on
  let o = level (xor k ok)
  apply hint arr
  return $! Node (k .&. unsafeShiftL 0xfffffffffffffff0 o) o (mask k o .|. mask ok o) arr

-- O(1) remove the _entire_ branch containing a given node from this tree, in situ
unplug :: Hint s -> Key -> Node s a -> ST s (Node s a)
unplug hint k on@(Full ok n as)
  | wd >= 0xf = return on
  | d <- fromIntegral wd = Node ok n (complement (unsafeShiftL 1 d)) <$> deleteSmallArray hint as d
  where !wd = unsafeShiftR (xor k ok) n
unplug hint !k on@(Node ok n m as)
  | wd >= 0xf = return on
  | !b <- unsafeShiftL 1 (fromIntegral wd), m .&. b /= 0, p <- index m b =
    if sizeOfSmallMutableArray as == 2
     then readSmallArray as (1-p) -- keep the other node
     else Node ok n (m .&. complement b) <$> deleteSmallArray hint as p
  | otherwise = return on
  where !wd = unsafeShiftR (xor k ok) n
unplug _ _ on = return on

canonical :: WordMap a -> Maybe (FrozenNode a)
canonical wm = runST $ case thaw wm of
  WordMap _ 0 Nothing _ -> return Nothing
  WordMap k _ mv ns -> Just . reallyUnsafeFreezeNode <$> replugPath cold k 0 (sizeOfSmallMutableArray ns) mv ns

-- O(1) plug a child node directly into an open parent node
-- carefully retains identity in case we plug what is already there back in
plug :: Hint s -> Key -> Node s a -> Node s a -> ST s (Node s a)
plug hint k z on@(Node ok n m as)
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
        False -> do -- this is a frozen node
          !oz <- readSmallArray as odm
          if ptrEq oz z
            then return on -- but we arent changing it
            else do -- here we are, and we need to copy on write
              bs <- cloneSmallMutableArray as 0 odm 
              writeSmallArray bs odm z
              apply hint bs
              return (Node ok n m bs)
  where wd = unsafeShiftR (xor k ok) n
plug hint k z on@(Full ok n as)
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
            return (Full ok n bs)
  where wd = unsafeShiftR (xor k ok) n
plug hint k z on@(Tip ok _) = fork hint k z ok on

-- | Given @k@ located under @acc@, @plugPath k i t acc ns@ plugs acc recursively into each of the nodes
-- of @ns@ from @[i..t-1]@ from the bottom up
plugPath :: Hint s -> Key -> Int -> Int -> Node s a -> SmallMutableArray s (Node s a) -> ST s (Node s a)
plugPath hint !k !i !t !acc !ns
  | i < t     = do
    x <- readSmallArray ns i
    y <- plug hint k acc x
    plugPath hint k (i+1) t y ns
  | otherwise = return acc

-- this recurses into @plugPath@ deliberately.
unplugPath :: Hint s -> Key -> Int -> Int -> SmallMutableArray s (Node s a) -> ST s (Node s a)
unplugPath hint k i t ns = do
  x <- readSmallArray ns i
  y <- unplug hint k x
  plugPath hint k (i+1) t y ns

replugPath :: PrimMonad m => Hint (PrimState m) -> Key -> Int -> Int -> Maybe v -> SmallMutableArray (PrimState m) (Node (PrimState m) v) -> m (Node (PrimState m) v)
replugPath hint k i t (Just v) ns = primToPrim $ plugPath hint k i t (Tip k v) ns
replugPath hint k i t Nothing ns  = primToPrim $ unplugPath hint k i t ns

unI# :: Int -> Int#
unI# (I# i) = i

-- create a 1-hole context at key k, destroying any previous contents of that position.

-- do we want to make this eager at scrubbing the parent pointers?

focusHint :: PrimMonad m => Hint (PrimState m) -> Key -> TWordMap (PrimState m) a -> m (TWordMap (PrimState m) a)
focusHint hint k0 wm0@(WordMap ok0 m0 mv0 ns0@(SmallMutableArray ns0#))
  | k0 == ok0 = return wm0 -- keys match, easy money
  | m0 == 0 = case mv0 of
    Nothing -> return (WordMap k0 0 Nothing emptySmallMutableArray)
    Just v  -> do
      ns <- newSmallArray 1 (Tip ok0 v)
      apply hint ns
      return $! WordMap k0 (unsafeShiftL 1 (unsafeShiftR (level (xor ok0 k0)) 2)) Nothing ns
  | kept <- m0 .&. unsafeShiftL 0xfffe (unsafeShiftR (level (xor ok0 k0)) 2)
  , nkept@(I# nkept#) <- popCount kept
  , top@(I# top#) <- sizeOfSmallMutableArray ns0 - nkept
  = do
    root <- replugPath hint ok0 0 top mv0 ns0
    primitive $ \s -> case go k0 nkept# root s of
      (# s', ms, m#, omv #) -> case copySmallMutableArray# ns0# top# ms (sizeofSmallMutableArray# ms -# nkept#) nkept# s' of -- we're copying nkept
        s'' -> case hint ms s'' of
          s''' -> (# s''', WordMap k0 (kept .|. W16# m#) omv (SmallMutableArray ms) #)
  where
    deep :: Key -> Int# -> SmallMutableArray# s (Node s a) -> Int# -> Node s a -> Int# -> State# s ->
      (# State# s, SmallMutableArray# s (Node s a), Word#, Maybe a #)
    deep k h# as d# on n# s = case readSmallArray# as d# s of
      (# s', on' #) -> case go k (h# +# 1#) on' s' of
        (# s'', ms, m#, mv #) -> case writeSmallArray# ms (sizeofSmallMutableArray# ms -# h# -# 1#) on s'' of
          s''' -> case unsafeShiftL 1 (unsafeShiftR (I# n#) 2) .|. W16# m# of
            W16# m'# -> (# s''', ms, m'#, mv #)

    shallow :: Int# -> Node s a -> Int# -> Maybe a -> State# s ->
      (# State# s, SmallMutableArray# s (Node s a), Word#, Maybe a #)
    shallow h# on n# mv s = case newSmallArray# (h# +# 1#) on s of
      (# s', ms #) -> case unsafeShiftL 1 (unsafeShiftR (I# n#) 2) of
        W16# m# -> (# s', ms, m#, mv #)

    go :: Key -> Int# -> Node s a -> State# s -> (# State# s, SmallMutableArray# s (Node s a), Word#, Maybe a #)
    go k h# on@(Full ok n@(I# n#) (SmallMutableArray as)) s
      | wd > 0xf  = shallow h# on (unI# (level okk)) Nothing s -- we're a sibling of what we recursed into  -- [Displaced Full]
      | otherwise = deep k h# as (unI# (fromIntegral wd)) on n# s                                           -- Parent Full : ..
      where !okk = xor k ok
            !wd = unsafeShiftR okk n
    go k h# on@(Node ok n@(I# n#) m (SmallMutableArray as)) s
      | wd > 0xf = shallow h# on (unI# (level okk)) Nothing s                                            -- [Displaced Node]
      | !b <- unsafeShiftL 1 (fromIntegral wd), m .&. b /= 0 = deep k h# as (unI# (index m b)) on n# s   -- Parent Node : ..
      | otherwise = shallow h# on n# Nothing s                                                           -- [Node]
      where !okk = xor k ok
            !wd = unsafeShiftR okk n
    go k h# on@(Tip ok v) s 
      | k == ok = case newSmallArray# h# undefined s of (# s', ms #) -> (# s', ms, int2Word# 0#, Just v #)
      | otherwise = shallow h# on (unI# (level (xor k ok))) Nothing s -- [Displaced Tip]

modify :: (forall s. TWordMap s a -> ST s (TWordMap s b)) -> WordMap a -> WordMap b
modify f wm = runST $ do
  mwm <- f (thaw wm)
  unsafeFreeze mwm
{-# INLINE modify #-}

focusM :: PrimMonad m => Key -> TWordMap (PrimState m) a -> m (TWordMap (PrimState m) a)
focusM = focusHint warm
{-# INLINE focusM #-}

focus :: Key -> WordMap a -> WordMap a
focus k = modify (focusHint cold k)

insertHint :: PrimMonad m => Hint (PrimState m) -> Key -> a -> TWordMap (PrimState m) a -> m (TWordMap (PrimState m) a)
insertHint hint k v wm@(WordMap ok _ mv _)
  | k == ok, Just ov <- mv, ptrEq v ov = return wm
  | otherwise = do
    wm' <- focusHint hint k wm 
    return $! wm' { fingerValue = Just v }
{-# INLINE insertHint #-}

insertM :: PrimMonad m => Key -> a -> TWordMap (PrimState m) a -> m (TWordMap (PrimState m) a)
insertM = insertHint warm
{-# INLINE insertM #-}

insert :: Key -> a -> WordMap a -> WordMap a
insert k v = modify (insertHint cold k v)
{-# INLINE insert #-}

deleteHint :: PrimMonad m => Hint (PrimState m) -> Key -> TWordMap (PrimState m) a -> m (TWordMap (PrimState m) a)
deleteHint hint k wm = focusHint hint k wm >>= \ wm' -> case fingerValue wm' of
  Nothing -> return wm'
  _       -> return $! wm' { fingerValue = Nothing }
{-# INLINE deleteHint #-}

deleteM :: PrimMonad m => Key -> TWordMap (PrimState m) a -> m (TWordMap (PrimState m) a)
deleteM = deleteHint warm
{-# INLINE deleteM #-}

delete :: Key -> WordMap a -> WordMap a
delete k = modify (deleteHint cold k)
{-# INLINE delete #-}

--------------------------------------------------------------------------------
-- * Instances
--------------------------------------------------------------------------------

instance IsList (WordMap a) where
  type Item (WordMap a) = (Word64, a)

  toList = ifoldr (\i a r -> (i, a): r) []
  {-# INLINE toList #-}

  -- fromList = foldl' (\r (k,v) -> insert k v r) empty

  fromList xs = runST $ do
     o <- foldM (\r (k,v) -> insertM k v r) emptyM xs
     unsafeFreeze o
  {-# INLINE fromList #-}

  fromListN _ = fromList
  {-# INLINE fromListN #-}

-- stuff to eventually clean up and reintroduce
      
type instance Index (WordMap a) = Key
type instance IxValue (WordMap a) = a

instance At (WordMap a) where
  at k f wm = let c = focus k wm in f (lookup k wm) <&> \mv' -> c { frozenFingerValue = mv' }
  {-# INLINE at #-}

instance Ixed (WordMap a) where
  ix k f wm = case lookup k wm of
    Nothing -> pure wm
    Just v  -> let c = focus k wm in f v <&> \v' -> c { frozenFingerValue = Just v' }

instance NFData a => NFData (FrozenNode a) where
  rnf (FrozenFull _ _ a)   = rnf a
  rnf (FrozenNode _ _ _ a) = rnf a
  rnf (FrozenTip _ v)      = rnf v

instance NFData a => NFData (WordMap a) where
  rnf (FrozenWordMap _ _ mv as) = rnf mv `seq` rnf as

instance AsEmpty (WordMap a) where
  _Empty = prism (const empty) $ \s -> case s of
    FrozenWordMap _ 0 Nothing _ -> Right ()
    t -> Left t

instance AsEmpty (TWordMap s a) where
  _Empty = prism (const emptyM) $ \s -> case s of
    WordMap _ 0 Nothing _ -> Right ()
    t -> Left t

instance FunctorWithIndex Word64 WordMap where
  imap f (FrozenWordMap k n mv as) = FrozenWordMap k n (fmap (f k) mv) (fmap (imap f) as)

instance FunctorWithIndex Word64 FrozenNode where
  imap f (FrozenNode k n m as) = FrozenNode k n m (fmap (imap f) as)
  imap f (FrozenTip k v)       = FrozenTip k (f k v)
  imap f (FrozenFull k n as)   = FrozenFull k n (fmap (imap f) as)

instance Foldable WordMap where
  fold wm      = foldMap fold (canonical wm)
  foldMap f wm = foldMap (foldMap f) (canonical wm)
  null (FrozenWordMap _ 0 Nothing _) = True
  null _                       = False

instance FoldableWithIndex Word64 WordMap where
  ifoldMap f wm = foldMap (ifoldMap f) (canonical wm)

instance FoldableWithIndex Word64 FrozenNode where
  ifoldMap f (FrozenNode _ _ _ as) = foldMap (ifoldMap f) as
  ifoldMap f (FrozenTip k v) = f k v
  ifoldMap f (FrozenFull _ _ as) = foldMap (ifoldMap f) as

instance Eq v => Eq (WordMap v) where
  as == bs = Exts.toList as == Exts.toList bs

instance Ord v => Ord (WordMap v) where
  compare as bs = compare (Exts.toList as) (Exts.toList bs)

-- TODO: Traversable, TraversableWithIndex Word64 WordMap
