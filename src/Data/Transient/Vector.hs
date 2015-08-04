{-# LANGUAGE CPP #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE DeriveTraversable #-}

module Data.Transient.Vector where

import Control.Applicative
import Control.Exception
import Control.Monad
import Control.Monad.Primitive
import Data.Bits
import Data.Monoid
import Data.Primitive.ByteArray
import Data.Primitive.MutVar
import Data.Transient.Primitive.SmallArray
import GHC.Exts

data Node a 
  = Sparse !(SmallArray (Node a)) !ByteArray
  | Dense  !Int !(SmallArray (Node a))
  | Leaf   !(SmallArray a)
  deriving (Functor, Foldable, Traversable)

data Vector a = Root !Int !(Node a)
  deriving (Functor, Traversable)

instance Foldable Vector where
  foldMap f (Root _ xs) = foldMap f xs
  foldr f z (Root _ xs) = foldr f z xs
  foldl f z (Root _ xs) = foldl f z xs
  length (Root n _) = n
  null (Root n _) = n == 0

(!) :: Vector a -> Int -> a
(!) (Root n r0) k0 | k0 >= 0 && k0 < n = go k0 r0 where
  go k (Sparse m ks) = case pos k ks of
    (# i, k' #) -> go k' (indexSmallArray m i)
  go k (Dense h m) = go k (indexSmallArray m (unsafeShiftR k h .&. 0xf))
  go k (Leaf m)    = indexSmallArray m (k .&. 0xf)
(!) _ k0 = throw $ IndexOutOfBounds (show k0)

pos :: Int -> ByteArray -> (# Int, Int #)
pos !b q = go 0 where
  go !i
    | o < b = go (i + 1)
    | otherwise = (# i, o - b #)
    where o = indexByteArray q i

instance Monoid (Vector a) where
  mempty = empty
  mappend = (<|>) 

instance Applicative Vector where
  pure = return
  -- we could build an lcm (length n * length m) mutable vector, and then tile the stuff through it
  -- and peasant multiply it gcd (length n * length m)
  m <*> n = foldMap (<$> n) m

instance Alternative Vector where
  empty = Root 0 (Leaf (fromList []))
  Root m l <|> Root n r = Root (m + n) (undefined l r) -- TODO

instance Monad Vector where
  return a = Root 1 (Leaf (fromList [a]))
  m >>= f = foldMap f m
  
instance MonadPlus Vector where
  mzero = empty
  mplus = (<|>)

cons :: a -> Vector a -> Vector a
cons a r = pure a <> r

snoc :: Vector a -> a -> Vector a
snoc r a = r <> pure a

uncons :: Vector a -> Maybe (a, Vector a)
uncons = undefined -- TODO

data TNode s a
  = TSparse !(SmallMutableArray s (TNode s a)) !(MutableByteArray s)
  | TDense !Int !(SmallMutableArray s (TNode s a))
  | TLeaf !(SmallMutableArray s a)
  | Thaw (Node a)

data TRoot s a
  = TRoot !Int !(TNode s a)
  | TEmpty

newtype TVector s a = TVector (MutVar s (TRoot s a))

#ifndef HLINT
type role TVector nominal representational
type role TNode nominal representational
type role TRoot nominal representational
#endif

thaw :: PrimMonad m => Vector a -> m (TVector (PrimState m) a)
thaw (Root m v) = TVector <$> newMutVar (TRoot m (Thaw v))

{-
freeze (TVector r) = readMutVar r >>= \case
    TRoot m v -> Root m <$> go v
  where
    go (TSparse as bs) = do
      cloneSmallArray as 0 (sizeOf
-}
