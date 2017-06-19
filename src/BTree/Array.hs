{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE MagicHash #-}

module BTree.Array 
  (
  ) where

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

