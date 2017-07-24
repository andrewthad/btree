{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE BangPatterns #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module BTree
  ( BTree
  , Context(..)
  , lookup
  , insert
  , modifyWithM
  , new
  , foldrWithKey
  , toAscList
  , fromList
  , debugMap
  ) where

import Prelude hiding (lookup)
import Data.Primitive (Prim)
import Control.Monad.ST
import Data.Primitive.MutVar

import qualified BTree.Linear as BTL

data BTree s k v = BTree
  !(MutVar s (BTL.BTree s k v)) -- The actual B Tree
  !(Context s) -- Context

newtype Context s = Context (BTL.Context s)

new :: (Prim k, Prim v)
  => Context s -- ^ Max number of children per node
  -> ST s (BTree s k v)
new outerCtx@(Context ctx) = do
  rootRef <- newMutVar =<< BTL.new ctx
  return (BTree rootRef outerCtx)

lookup :: forall s k v. (Ord k, Prim k, Prim v)
  => BTree s k v -> k -> ST s (Maybe v)
lookup (BTree nodeRef (Context ctx)) k = do 
  root <- readMutVar nodeRef
  BTL.lookup ctx root k

insert :: (Ord k, Prim k, Prim v)
  => BTree s k v
  -> k
  -> v
  -> ST s ()
insert m k v = modifyWithM m k (\_ -> return v) >> return ()

-- | This is provided for completeness but is not something
--   typically useful in producetion code.
toAscList :: forall s k v. (Ord k, Prim k, Prim v)
  => BTree s k v
  -> ST s [(k,v)]
toAscList (BTree rootRef (Context ctx))
  = BTL.toAscList ctx =<< readMutVar rootRef

fromList :: (Ord k, Prim k, Prim v)
  => Context s -> [(k,v)] -> ST s (BTree s k v)
fromList ctxOuter@(Context ctx) xs = do
  root <- BTL.fromList ctx xs
  rootRef <- newMutVar root
  return (BTree rootRef ctxOuter)

foldrWithKey :: forall s k v b. (Ord k, Prim k, Prim v)
  => (k -> v -> b -> ST s b)
  -> b
  -> BTree s k v
  -> ST s b
foldrWithKey f b0 (BTree rootRef (Context ctx)) =
  readMutVar rootRef >>= BTL.foldrWithKey f b0 ctx

modifyWithM :: forall s k v. (Ord k, Prim k, Prim v)
  => BTree s k v
  -> k
  -> (Maybe v -> ST s v)
  -> ST s v
modifyWithM (BTree rootRef (Context ctx)) k alter = do
  root <- readMutVar rootRef
  (v,newRoot) <- BTL.modifyWithM ctx root k alter
  writeMutVar rootRef newRoot
  return v

debugMap :: forall s k v. (Prim k, Prim v, Show k, Show v)
  => BTree s k v
  -> ST s String
debugMap (BTree rootRef (Context ctx))
  = BTL.debugMap ctx =<< readMutVar rootRef

