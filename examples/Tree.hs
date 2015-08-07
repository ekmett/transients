{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE RoleAnnotations #-}

import Control.Exception
import Control.Monad.Primitive
import Control.Monad.ST
import Control.Monad.ST.Unsafe
import Data.Primitive.MutVar

data FrozenTransient = FrozenTransient deriving (Show, Exception)

throwFrozenTransient :: PrimMonad m => m a
throwFrozenTransient = unsafePrimToPrim $ throwIO FrozenTransient

data Tree a
  = Tip
  | Bin a (Tree a) (Tree a) 
  deriving (Functor,Foldable, Traversable,Show,Read,Eq,Ord)

data TNode s a
  = Thaw (Tree a)
  | TBin a !(TTree s a) !(TTree s a)
  | Frozen
  deriving (Eq)

newtype TTree s a = TTree (MutVar s (TNode s a)) deriving (Eq)

#ifndef HLINT
type role TNode nominal representational
type role TTree nominal representational
#endif

-- O(1) worst-case
thaw :: PrimMonad m => Tree a -> m (TTree (PrimState m) a)
thaw s = TTree <$> newMutVar (Thaw s)

-- O(n) in the number of mutable nodes we've created
freeze :: PrimMonad m => TTree (PrimState m) a -> m (Tree a)
freeze (TTree m) = readMutVar m >>= \case
  Thaw s -> return s
  TBin a l r -> Bin a <$> freeze l <*> freeze r
  Frozen -> throwFrozenTransient

-- O(1) worst-case -- the sub-freezes are charged to subsequent accesses
unsafeFreeze :: PrimMonad m => TTree (PrimState m) a -> m (Tree a)
unsafeFreeze = primToPrim . go where
  go (TTree m) = atomicModifyMutVar m ((,) Frozen) >>= \case
    Thaw s -> return s
    TBin a l r -> Bin a <$> unsafeInterleaveST (go l) <*> unsafeInterleaveST (go r)
    Frozen -> throwFrozenTransient

reallyUnsafeFreeze :: PrimMonad m => TTree (PrimState m) a -> m (Tree a)
reallyUnsafeFreeze = primToPrim . go where 
  go (TTree m) = readMutVar m >>= \case
    Thaw s -> return s
    TBin a l r -> Bin a <$> unsafeInterleaveST (go l) <*> unsafeInterleaveST (go r)
    Frozen -> throwFrozenTransient

query :: (Tree a -> r) -> TTree s a -> m r
query f s = f <$> freeze s

modify :: (forall s. TTree s a -> ST s ()) -> Tree a -> Tree a
modify f s = runST $ do
  ms <- thaw s
  f ms
  reallyUnsafeFreeze ms

insert :: Ord a => a -> Tree a -> Tree a
insert a Tip = Bin a Tip Tip
insert a (Bin b l r) = case compare a b of
  LT -> Bin b (insert a l) r
  EQ -> Bin a l r
  GT -> Bin b l (insert a r)

ttree :: PrimMonad m => TNode (PrimState m) a -> m (TTree (PrimState m) a)
ttree n = TTree <$> newMutVar n

tip :: PrimMonad m => m (TTree (PrimState m) a)
tip = thaw Tip

insertThawM :: (PrimMonad m, Ord a) => a -> Tree a -> m (TNode (PrimState m) a)
insertThawM a Tip = TBin a <$> thaw Tip <*> thaw Tip
insertThawM a (Bin b l r) = case compare a b of
  LT -> TBin b <$> (insertThawM a l >>= ttree) <*> thaw r
  EQ -> TBin a <$> thaw l <*> thaw r
  GT -> TBin b <$> thaw l <*> (insertThawM a r >>= ttree)

insertM :: (PrimMonad m, Ord a) => a -> TTree (PrimState m) a -> m ()
insertM a (TTree m) = readMutVar m >>= \case
  Thaw s -> insertThawM a s >>= writeMutVar m
  TBin b l r -> case compare a b of
    LT -> insertM a l
    EQ -> writeMutVar m (TBin a l r)
    GT -> insertM a r
