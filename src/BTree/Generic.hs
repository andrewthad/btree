{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}

{-# OPTIONS_GHC -Wall -Werror -fno-warn-unused-imports #-}

module BTree.Generic
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
import Data.Primitive hiding (fromList)
import Data.Primitive.MutVar
import Control.Monad
import Data.Foldable (foldlM)
import Data.Kind (Type)
import Data.Primitive.PrimArray
import Data.Primitive.Array
import Data.Primitive.Compact
import Data.Primitive.Types
import Control.Monad.Primitive
import Data.Proxy
import Data.Primitive.Compact
import GHC.Prim
import GHC.Types

import Data.Primitive.PrimArray
import Control.Monad.ST

data Context s = Context
  { contextDegree :: {-# UNPACK #-} !Int
  }

data BTree (t :: Compactedness) (b :: Boxedness) s k v = BTree
  !(MutVar s Int) -- current number of keys in this node
  !(MutablePrimArray s k)
  !(RepresentedContents t b s k v)


data Compactedness = Compacted Type | Uncompacted
data Boxedness = Boxed | Unboxed

class Represented (t :: Compactedness) (b :: Boxedness) where
  type RepresentedContainer t b a :: *
  type RepresentedArray t b :: * -> * -> *
  type RepresentedToken t b :: *
  type RepresentedContents t b s v :: TYPE ('SumRep '[ 'UnliftedRep, 'UnliftedRep])
  representedNewPrimArray :: (PrimMonad m, Prim a)
    => Proxy# t 
    -> Proxy# b
    -> Proxy# a 
    -> RepresentedToken t b
    -> Int
    -> m (RepresentedContainer t b (MutablePrimArray (PrimState m) a))
  representedNewArray :: PrimMonad m
    => Proxy# t
    -> Proxy# b
    -> Proxy# a
    -> RepresentedToken t b
    -> Int
    -> m (RepresentedContainer t b (RepresentedArray t b (PrimState m) a))

instance Represented 'Uncompacted 'Boxed where
  type RepresentedContainer 'Uncompacted 'Boxed a = a
  type RepresentedArray 'Uncompacted 'Boxed = MutableArray
  type RepresentedToken 'Uncompacted 'Boxed = ()
  type RepresentedContents 'Uncompacted 'Boxed s v = (# MutableArray# | #)
  representedNewPrimArray _ _ _ _ n = newPrimArray n
  representedNewArray _ _ _ _ n = newArray n undefinedElement

instance Represented ('Compacted c) 'Boxed where
  type RepresentedContainer ('Compacted c) 'Boxed a = CompactValue c a
  type RepresentedArray ('Compacted c) 'Boxed = CompactMutableArray c
  type RepresentedToken ('Compacted c) 'Boxed = Token c
  representedNewPrimArray _ _ _ token n =
    newPrimArray n >>= newCompactValue token
  representedNewArray _ _ _ token n = newCompactArray token n

undefinedElement :: a
undefinedElement = error "btree: accessed uninitialized element, implementation mistake" 
{-# NOINLINE undefinedElement #-}

