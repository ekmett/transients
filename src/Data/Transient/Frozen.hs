{-# LANGUAGE TypeFamilies, RankNTypes, KindSignatures #-}
module Data.Transient.Frozen 
  ( Frozen(..)
  ) where

import Control.Monad.Primitive
import Control.Monad.ST

class Frozen t where
  type Transient t :: * -> *

  -- | *O(1)* amortized conversion from a mutable structure to an immutable one
  freeze :: PrimMonad m => Transient t (PrimState m) -> m t

  -- | *O(1)* worst-case conversion from an immutable structure to a mutable one
  thaw   :: t -> Transient t s

  -- | *O(1) + modification time*, to modify an immutable structure with mutable operations.
  --
  -- The transient passed to this function is considered frozen
  modify :: (forall s. Transient t s -> ST s (Transient t s)) -> t -> t

  -- | *O(1) + query time* to query a mutable data structure with questions designed for its immutable sibling
  -- 
  -- This freezes the transient.
  query  :: PrimMonad m => (t -> r) -> Transient t (PrimState m) -> m r
