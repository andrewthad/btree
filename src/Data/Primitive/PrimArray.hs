{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Data.Primitive.PrimArray
  ( PrimArray(..)
  , MutablePrimArray(..)
  , newPrimArray
  , readPrimArray
  , writePrimArray
  , copyMutablePrimArray
  ) where

import GHC.Prim
import GHC.Int
import Data.Primitive
import Control.Monad.Primitive

-- | Primitive arrays
data PrimArray = ByteArray ByteArray#

-- | Mutable primitive arrays associated with a primitive state token
data MutablePrimArray s a = MutablePrimArray (MutableByteArray# s)

newPrimArray :: forall m a. (PrimMonad m, Prim a) => Int -> m (MutablePrimArray (PrimState m) a)
{-# INLINE newPrimArray #-}
newPrimArray (I# n#)
  = primitive (\s# -> 
      case newByteArray# (n# *# sizeOf# (undefined :: a)) s# of
        (# s'#, arr# #) -> (# s'#, MutablePrimArray arr# #)
    )

readPrimArray :: (Prim a, PrimMonad m) => MutablePrimArray (PrimState m) a -> Int -> m a
{-# INLINE readPrimArray #-}
readPrimArray (MutablePrimArray arr#) (I# i#)
  = primitive (readByteArray# arr# i#)

writePrimArray ::
     (Prim a, PrimMonad m)
  => MutablePrimArray (PrimState m) a
  -> Int
  -> a
  -> m ()
{-# INLINE writePrimArray #-}
writePrimArray (MutablePrimArray arr#) (I# i#) x
  = primitive_ (writeByteArray# arr# i# x)

-- | Copy part of a mutable byte array. The destination and
--   source are allowed to be the same.
copyMutablePrimArray :: forall m a.
     (PrimMonad m, Prim a)
  => MutablePrimArray (PrimState m) a -- ^ destination array
  -> Int -- ^ offset into destination array
  -> MutablePrimArray (PrimState m) a -- ^ source array
  -> Int -- ^ offset into source array
  -> Int -- ^ number of bytes to copy
  -> m ()
copyMutablePrimArray (MutablePrimArray dest) !destOff (MutablePrimArray source) !sourceOff !n =
  copyMutableByteArray
    (MutableByteArray dest) (sz * destOff)
    (MutableByteArray source) (sz * sourceOff)
    (sz * n)
  where
  sz = sizeOf (undefined :: a)


