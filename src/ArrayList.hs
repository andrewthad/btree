{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE UnboxedTuples #-}

{-# OPTIONS_GHC -Wall #-}

module ArrayList
  ( ArrayList
  , with
  , new
  , pushR
  , popL
  , dropWhileL
  , dropL
  , dump
  , dumpList
  , clear
  ) where

import Foreign.Ptr
import Foreign.Storable
import Foreign.Marshal.Array
import Data.Primitive.PrimArray
import GHC.Prim (RealWorld)
import GHC.Int (Int(..))
import GHC.Ptr (Ptr(..))
import GHC.IO (IO(..))
import GHC.Prim ((*#),copyAddrToByteArray#)
import Data.Primitive hiding (sizeOf)
import Data.Primitive.Types
import Data.Bits (unsafeShiftR)
import qualified Data.Primitive as PM
import qualified Foreign.Marshal.Alloc as FMA

data ArrayList a = ArrayList
  {-# UNPACK #-} !Int -- start index (in elements)
  {-# UNPACK #-} !Int -- used length (in elements)
  {-# UNPACK #-} !Int -- buffer length (in elements)
  {-# UNPACK #-} !(Ptr a) -- all the data

instance Storable (ArrayList a) where
  sizeOf _ = wordSz * 4
  alignment _ = wordSz
  peek ptr = ArrayList
    <$> peek (castPtr ptr)
    <*> peek (plusPtr ptr wordSz)
    <*> peek (plusPtr ptr (wordSz + wordSz))
    <*> peek (plusPtr ptr (wordSz + wordSz + wordSz))
  poke ptr (ArrayList a b c d) = do
    poke (castPtr ptr) a
    poke (plusPtr ptr wordSz) b
    poke (plusPtr ptr (wordSz + wordSz)) c
    poke (plusPtr ptr (wordSz + wordSz + wordSz)) d

wordSz :: Int
wordSz = sizeOf (undefined :: Int)
  
initialSize :: Int
initialSize = 4

with :: Storable a => (ArrayList a -> IO (ArrayList a,b)) -> IO b
with f = do
  initial <- new
  (final,a) <- f initial
  free final
  return a

new :: forall a. Storable a => IO (ArrayList a)
new = do
  ptr <- FMA.mallocBytes (sizeOf (undefined :: a) * initialSize)
  return (ArrayList 0 0 initialSize ptr)

pushR :: forall a. Storable a => ArrayList a -> a -> IO (ArrayList a)
pushR (ArrayList start len bufLen ptr) a = if start + len < bufLen
  then do
    poke (advancePtr ptr (start + len)) a
    return (ArrayList start (len + 1) bufLen ptr)
  else if
      -- this quarter case may not actually be needed since
      -- the pop functions have to check for this.
    | len < quarter bufLen -> do
        newPtr <- FMA.mallocBytes (sizeOf (undefined :: a) * div bufLen 2)
        moveArray newPtr (advancePtr ptr start) len
        FMA.free ptr
        poke (advancePtr newPtr len) a
        return (ArrayList 0 (len + 1) (div bufLen 2) newPtr)
    | len < half bufLen -> do
        moveArray ptr (advancePtr ptr start) len
        poke (advancePtr ptr len) a
        return (ArrayList 0 (len + 1) bufLen ptr)
    | otherwise -> do
        newPtr <- FMA.mallocBytes (sizeOf (undefined :: a) * bufLen * 2)
        moveArray newPtr (advancePtr ptr start) len
        FMA.free ptr
        poke (advancePtr newPtr len) a
        return (ArrayList 0 (len + 1) (bufLen * 2) newPtr)

popL :: forall a. Storable a => ArrayList a -> IO (ArrayList a, Maybe a)
popL xs@(ArrayList start len bufLen ptr)
  | len < 1 = return (xs, Nothing)
  | otherwise = do
      a <- peek (advancePtr ptr start)
      newArrList <- minimizeMemory (ArrayList (start + 1) (len - 1) bufLen ptr)
      return (newArrList, Just a)

dropWhileL :: forall a. Storable a => ArrayList a -> (a -> Bool) -> IO (ArrayList a)
dropWhileL (ArrayList start len bufLen ptr) p = do
  let go :: Int -> IO Int
      go !i = if i < len
        then do
          a <- peek (advancePtr ptr (start + i))
          if p a
            then go (i + 1)
            else return i
        else return i
  dropped <- go 0
  let newArrList = ArrayList (start + dropped) (len - dropped) bufLen ptr
  minimizeMemory newArrList

dropL :: forall a. Storable a => ArrayList a -> Int -> IO (ArrayList a)
dropL (ArrayList start len bufLen ptr) n = do
  let m = min n len
  minimizeMemory $ ArrayList (start + m) (len - m) bufLen ptr

minimizeMemory :: forall a. Storable a => ArrayList a -> IO (ArrayList a)
minimizeMemory xs@(ArrayList start len bufLen ptr)
    -- we do not drop below a certain size, since then we would
    -- end up doing frequent reallocations.
  | bufLen <= initialSize = return xs
  | len < quarter bufLen = do
      newPtr <- FMA.mallocBytes (sizeOf (undefined :: a) * div bufLen 2)
      moveArray newPtr (advancePtr ptr start) len
      FMA.free ptr
      return (ArrayList 0 len (div bufLen 2) newPtr)
  | otherwise = return (ArrayList start len bufLen ptr)
  

{-# INLINE half #-}
half :: Int -> Int
half x = unsafeShiftR x 1

{-# INLINE quarter #-}
quarter :: Int -> Int
quarter x = unsafeShiftR x 2

-- | This should not be used in production code.
dumpList :: (Prim a, Storable a) => ArrayList a -> IO (ArrayList a, [a])
dumpList xs@(ArrayList _ len _ _) = do
  marr <- newPrimArray len
  newXs <- dump xs marr 0
  arr <- unsafeFreezePrimArray marr
  return (newXs,primArrayToList len arr)

primArrayToList :: forall a. Prim a => Int -> PrimArray a -> [a]
primArrayToList len arr = go 0
  where
  go :: Int -> [a]
  go !ix = if ix < len
    then indexPrimArray arr ix : go (ix + 1)
    else []
 

-- | Deletes all elements from the linked list, copying them
--   into the buffer specified by the pointer. Returns an
--   empty linked list.
dump :: forall a. (Prim a, Storable a) => ArrayList a -> MutablePrimArray RealWorld a -> Int -> IO (ArrayList a)
dump xs@(ArrayList start len _ ptr) marr ix = do
  copyPtrToPrimArray (plusPtr ptr (start * PM.sizeOf (undefined :: a))) marr ix len
  clear xs

copyPtrToPrimArray :: forall a. Prim a
  => Ptr a -> MutablePrimArray RealWorld a -> Int -> Int -> IO ()
copyPtrToPrimArray (Ptr addr#) (MutablePrimArray marr#) (I# start#) (I# len#) =
  IO $ \s -> case copyAddrToByteArray# addr# marr# (start# *# sizeOf# (undefined :: a)) (len# *# sizeOf# (undefined :: a)) s of
    s' -> (# s', () #)

clear :: Storable a => ArrayList a -> IO (ArrayList a)
clear xs@(ArrayList _ len _ _) = dropL xs len

-- | Final consumer of the ArrayList.
free :: ArrayList a -> IO ()
free (ArrayList _ _ _ ptr) = FMA.free ptr
  
