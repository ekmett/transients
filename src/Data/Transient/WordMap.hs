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

data Node s v 
  = Full {-# UNPACK #-} !Key {-# UNPACK #-} !Offset !(SmallMutableArray s (Node s v))
  | Node {-# UNPACK #-} !Key {-# UNPACK #-} !Offset {-# UNPACK #-} !Mask !(SmallMutableArray s (Node s v))
  | Tip  {-# UNPACK #-} !Key v


--------------------------------------------------------------------------------
-- * WordMaps
--------------------------------------------------------------------------------

newtype WordMap v = Frozen { thaw :: forall s. TWordMap s v }

-- | This is a transient WordMap.
data TWordMap s v = WordMap {-# UNPACK #-} !Key {-# UNPACK #-} !Mask !(Maybe v) {-# UNPACK #-} !(SmallMutableArray s (Node s v))

--------------------------------------------------------------------------------
-- * Transient WordMaps
--------------------------------------------------------------------------------

reallyUnsafeFreeze :: TWordMap s v -> WordMap v
reallyUnsafeFreeze = unsafeCoerce
{-# INLINE reallyUnsafeFreeze #-}

unsafeFreeze :: PrimMonad m => TWordMap (PrimState m) v -> m (WordMap v)
unsafeFreeze r@(WordMap _ _ _ ns) = primToPrim $ do
    go ns 
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

empty :: WordMap v
empty = Frozen emptyM
{-# NOINLINE empty #-}

emptySmallMutableArray :: SmallMutableArray s a
emptySmallMutableArray = runST $ unsafeCoerce <$> newSmallArray 0 undefined
{-# NOINLINE emptySmallMutableArray #-}

emptyM :: TWordMap s v
emptyM = WordMap 0 0 Nothing emptySmallMutableArray
{-# INLINE emptyM #-}

-- | Build a singleton Node
singleton :: Key -> v -> WordMap v
singleton k v = Frozen (singletonM k v)
{-# INLINE singleton #-}

singletonM :: Key -> v -> TWordMap s v
singletonM k v = WordMap k 0 (Just v) emptySmallMutableArray
{-# INLINE singletonM #-}

lookup :: Key -> WordMap v -> Maybe v
lookup k m = runST (lookupM k (thaw m))
{-# INLINEABLE lookup #-}

lookupM :: PrimMonad m => Key -> TWordMap (PrimState m) v -> m (Maybe v)
lookupM k0 (WordMap ok m mv mns)
  | k0 == ok = return mv
  | b <- apogee k0 ok = if
    | m .&. b == 0 -> return Nothing
    | otherwise    -> do
      x <- readSmallArray mns (index m b)
      primToPrim (lookupNodeM k0 x)
{-# INLINEABLE lookupM #-}

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

insertSmallArray :: Hint s -> Int -> a -> SmallMutableArray s a -> ST s (SmallMutableArray s a)
insertSmallArray hint k a i = do
  let n = sizeOfSmallMutableArray i
  o <- newSmallArray (n + 1) a
  copySmallMutableArray  o 0 i 0 k
  copySmallMutableArray  o (k+1) i k (n-k)
  apply hint o
  return o
{-# INLINEABLE insertSmallArray #-}

deleteSmallArray :: Hint s -> Int -> SmallMutableArray s a -> ST s (SmallMutableArray s a)
deleteSmallArray hint k i = do
  let n = sizeOfSmallMutableArray i
  o <- newSmallArray (n - 1) undefined
  copySmallMutableArray o 0 i 0 k
  copySmallMutableArray o k i (k+1) (n-k-1)
  apply hint o
  return o
{-# INLINEABLE deleteSmallArray #-}

node :: Key -> Offset -> Mask -> SmallMutableArray s (Node s v) -> Node s v
node k o 0xffff a = Full k o a
node k o m a      = Node k o m a
{-# INLINE node #-}

fork :: Hint s -> Key -> Node s v -> Key -> Node s v -> ST s (Node s v)
fork hint k n ok on = do
  arr <- newSmallArray 2 n
  writeSmallArray arr (fromEnum (k < ok)) on
  let o = level (xor k ok)
  apply hint arr
  return $! Node (k .&. unsafeShiftL 0xfffffffffffffff0 o) o (mask k o .|. mask ok o) arr

-- O(1) remove the _entire_ branch containing a given node from this tree, in situ
unplug :: Hint s -> Key -> Node s v -> ST s (Node s v)
unplug hint k on@(Full ok n as)
  | wd >= 0xf = return on
  | d <- fromIntegral wd = Node ok n (complement (unsafeShiftL 1 d)) <$> deleteSmallArray hint d as
  where !wd = unsafeShiftR (xor k ok) n
unplug hint !k on@(Node ok n m as)
  | wd >= 0xf = return on
  | !b <- unsafeShiftL 1 (fromIntegral wd), m .&. b /= 0, p <- index m b =
    if sizeOfSmallMutableArray as == 2
     then readSmallArray as (1-p) -- keep the other node
     else Node ok n (m .&. complement b) <$> deleteSmallArray hint p as
  | otherwise = return on
  where !wd = unsafeShiftR (xor k ok) n
unplug _ _ on = return on

canonical :: PrimMonad m => Hint (PrimState m) -> WordMap v -> m (Maybe (Node (PrimState m) v))
canonical hint wm = primToPrim $ case thaw wm of
  WordMap _ 0 Nothing _  -> return Nothing
  WordMap k _ Nothing ns -> Just <$> unplugPath hint k 0 (sizeOfSmallMutableArray ns) ns
  WordMap k _ (Just v) ns -> Just <$> plugPath hint k 0 (sizeOfSmallMutableArray ns) (Tip k v) ns

-- O(1) plug a child node directly into an open parent node
-- carefully retains identity in case we plug what is already there back in
plug :: Hint s -> Key -> Node s v -> Node s v -> ST s (Node s v)
plug hint k z on@(Node ok n m as)
  | wd > 0xf = fork hint k z ok on
  | otherwise = do
    let d   = fromIntegral wd
        b   = unsafeShiftL 1 d
        odm = index m b
    if m .&. b == 0
      then node ok n (m .|. b) <$> insertSmallArray hint odm z as
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
plugPath :: Hint s -> Key -> Int -> Int -> Node s v -> SmallMutableArray s (Node s v) -> ST s (Node s v)
plugPath hint !k !i !t !acc !ns
  | i < t     = do
    x <- readSmallArray ns i
    y <- plug hint k acc x
    plugPath hint k (i+1) t y ns
  | otherwise = return acc

-- this recurses into @plugPath@ deliberately.
unplugPath :: Hint s -> Key -> Int -> Int -> SmallMutableArray s (Node s v) -> ST s (Node s v)
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

focusHint :: PrimMonad m => Hint (PrimState m) -> Key -> TWordMap (PrimState m) v -> m (TWordMap (PrimState m) v)
focusHint hint k0 wm0@(WordMap ok0 m0 mv0 ns0@(SmallMutableArray ns0#))
  | k0 == ok0 = return wm0 -- keys match, easy money
  | m0 == 0 = case mv0 of
    Nothing -> return (WordMap k0 0 Nothing ns0) -- note: ns0 is empty, we could use a global 'emptySmallMutableArray' here
    Just v  -> WordMap k0 (unsafeShiftL 1 (unsafeShiftR (level (xor ok0 k0)) 2)) Nothing <$> newSmallArray 1 (Tip ok0 v)
  | kept <- m0 .&. unsafeShiftL 0xfffe (unsafeShiftR (level (xor ok0 k0)) 2)
  , nkept@(I# nkept#) <- popCount kept
  , top@(I# top#) <- sizeOfSmallMutableArray ns0 - nkept
  = do
    root <- replugPath hint ok0 0 top mv0 ns0
    primitive $ \s -> case go k0 nkept# root s of
      (# s', ms, m#, omv #) -> case copySmallMutableArray# ns0# top# ms (sizeofSmallMutableArray# ms -# nkept#) nkept# s' of -- we're copying nkept
        s'' -> case hint ms s'' of
          s''' -> (# s'', WordMap k0 (kept .|. W16# m#) omv (SmallMutableArray ms) #)
  where
    deep :: Key -> Int# -> SmallMutableArray# s (Node s v) -> Int# -> Node s v -> Int# -> State# s ->
      (# State# s, SmallMutableArray# s (Node s v), Word#, Maybe v #)
    deep k h# as d# on n# s = case readSmallArray# as d# s of
      (# s', on' #) -> case go k (h# +# 1#) on' s' of
        (# s'', ms, m#, mv #) -> case writeSmallArray# ms (sizeofSmallMutableArray# ms -# h# -# 1#) on s'' of
          s''' -> case unsafeShiftL 1 (unsafeShiftR (I# n#) 2) .|. W16# m# of
            W16# m'# -> (# s''', ms, m'#, mv #)

    shallow :: Int# -> Node s v -> Int# -> Maybe v -> State# s ->
      (# State# s, SmallMutableArray# s (Node s v), Word#, Maybe v #)
    shallow h# on n# mv s = case newSmallArray# (h# +# 1#) on s of
      (# s', ms #) -> case unsafeShiftL 1 (unsafeShiftR (I# n#) 2) of
        W16# m# -> (# s', ms, m#, mv #)

    go :: Key -> Int# -> Node s v -> State# s -> (# State# s, SmallMutableArray# s (Node s v), Word#, Maybe v #)
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

modify :: (forall s. TWordMap s v -> ST s (TWordMap s v)) -> WordMap v -> WordMap v
modify f wm = runST $ do
  mwm <- f (thaw wm)
  unsafeFreeze mwm
{-# INLINE modify #-}

focusM :: PrimMonad m => Key -> TWordMap (PrimState m) v -> m (TWordMap (PrimState m) v)
focusM = focusHint warm
{-# INLINE focusM #-}

focus :: Key -> WordMap v -> WordMap v 
focus k = modify (focusHint cold k)

insertHint :: PrimMonad m => Hint (PrimState m) -> Key -> v -> TWordMap (PrimState m) v -> m (TWordMap (PrimState m) v)
insertHint hint k v wm@(WordMap ok _ mv _)
  | k == ok, Just ov <- mv, ptrEq v ov = return wm
  | otherwise = do
    WordMap ok' m' _ as' <- focusHint hint k wm 
    return $ WordMap ok' m' (Just v) as'
{-# INLINE insertHint #-}

insertM :: PrimMonad m => Key -> v -> TWordMap (PrimState m) v -> m (TWordMap (PrimState m) v)
insertM = insertHint warm
{-# INLINE insertM #-}

insert :: Key -> v -> WordMap v -> WordMap v
insert k v = modify (insertHint cold k v)
{-# INLINE insert #-}

deleteHint :: PrimMonad m => Hint (PrimState m) -> Key -> TWordMap (PrimState m) v -> m (TWordMap (PrimState m) v)
deleteHint hint k wm = focusHint hint k wm >>= \case
  wm'@(WordMap _ _ Nothing _) -> return wm'
  WordMap ok' m' _ as' -> return (WordMap ok' m' Nothing as')
{-# INLINE deleteHint #-}

deleteM :: PrimMonad m => Key -> TWordMap (PrimState m) v -> m (TWordMap (PrimState m) v)
deleteM = deleteHint warm
{-# INLINE deleteM #-}

delete :: Key -> WordMap v -> WordMap v
delete k = modify (deleteHint cold k)
{-# INLINE delete #-}

--------------------------------------------------------------------------------
-- * Instances
--------------------------------------------------------------------------------

instance NFData v => NFData (WordMap v) where
  rnf wm = runST $ case thaw wm of WordMap _ _ mv ns -> rnf mv `seq` array ns (sizeOfSmallMutableArray ns - 1)
    where
      array :: SmallMutableArray s (Node s v) -> Int -> ST s ()
      array ns i
        | i >= 0 = do
          x <- readSmallArray ns i
          node x
          array ns (i-1)
        | otherwise = return ()

      node :: Node s v -> ST s ()
      node (Node _ _ _ as) = array as (sizeOfSmallMutableArray as - 1)
      node (Full _ _ as) = array as 16
      node (Tip _ v) = rnf v `seq` return ()

instance IsList (WordMap v) where
  type Item (WordMap v) = (Word64, v)

{-
  toList = ifoldr (\i a r -> (i, a): r) []
  {-# INLINE toList #-}
-}

  fromList xs = runST $ do
     o <- foldM (\r (k,v) -> insertM k v r) emptyM xs
     unsafeFreeze o
  {-# INLINE fromList #-}

  fromListN _ = fromList
  {-# INLINE fromListN #-}

-- stuff to eventually clean up and reintroduce
      
{-

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

instance NFData v => NFData (Node s v) where
  rnf (Full _ _ a)   = rnf a
  rnf (Node _ _ _ a) = rnf a
  rnf (Tip _ v)      = rnf v

instance NFData v => NFData (WordMap v) where
  rnf (WordMap (Path _ _ as) mv) = rnf as `seq` rnf mv

instance AsEmpty (WordMap a) where
  _Empty = prism (const empty) $ \s -> case s of
    WordMap (Path _ 0 _) Nothing -> Right ()
    t -> Left t

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
-}

