{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE UnboxedTuples #-}

module ArrayList
  ( ArrayList
  , size
  , with
  , new
  , free
  , pushR
  , pushArrayR
  , popL
  , dropWhileL
  , dropWhileScanL
  , dropScanL
  , dropL
  , dump
  , dumpMap
  , dumpList
  , clear
  , showDebug
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
import BTree.Store (Initialize(..),Deinitialize(..))
import Control.Monad (when)
import qualified Data.Primitive as PM
import qualified Foreign.Marshal.Alloc as FMA
import qualified Foreign.Storable as FS

-- Special value for Ptr: If the pointer is null, then
-- it is understood that the ArrayList is of length 0.
-- For such an ArrayList, it is understood that
-- all of the fields should be 0.
data ArrayList a = ArrayList
  {-# UNPACK #-} !Int -- start index (in elements)
  {-# UNPACK #-} !Int -- used length (in elements)
  {-# UNPACK #-} !Int -- buffer length (in elements)
  {-# UNPACK #-} !(Ptr a) -- all the data

instance Storable (ArrayList a) where
  sizeOf _ = wordSz * 4
  alignment _ = wordSz
  {-# INLINE peek #-}
  peek ptr = ArrayList
    <$> peek (castPtr ptr)
    <*> peek (plusPtr ptr wordSz)
    <*> peek (plusPtr ptr (wordSz + wordSz))
    <*> peek (plusPtr ptr (wordSz + wordSz + wordSz))
  {-# INLINE poke #-}
  poke ptr (ArrayList a b c d) = do
    poke (castPtr ptr) a
    poke (plusPtr ptr wordSz) b
    poke (plusPtr ptr (wordSz + wordSz)) c
    poke (plusPtr ptr (wordSz + wordSz + wordSz)) d

instance Storable a => Initialize (ArrayList a) where
  {-# INLINE initialize #-}
  initialize (Ptr addr#) = setAddr (Addr addr#) 4 (0 :: Int)

wordSz :: Int
wordSz = PM.sizeOf (undefined :: Int)
  
initialSize :: Int
initialSize = 4

size :: ArrayList a -> Int
size (ArrayList _ len _ _) = len

with :: Storable a => (ArrayList a -> IO (ArrayList a,b)) -> IO b
with f = do
  initial <- new
  (final,a) <- f initial
  free final
  return a

new :: forall a. Storable a => IO (ArrayList a)
new = return (ArrayList 0 0 0 nullPtr)

{-# INLINABLE pushR #-}
pushR :: forall a. Storable a => ArrayList a -> a -> IO (ArrayList a)
pushR (ArrayList start len bufLen ptr) a = if start + len < bufLen
  then do
    poke (advancePtr ptr (start + len)) a
    return (ArrayList start (len + 1) bufLen ptr)
  else if
    | len == 0 -> do
        when (bufLen /= 0) (fail "ArrayList.pushR: invariant violated")
        when (start /= 0) (fail "ArrayList.pushR: invariant violated")
        when (ptr /= nullPtr) (fail "ArrayList.pushR: invariant violated")
        ptr <- FMA.mallocBytes (FS.sizeOf (undefined :: a) * initialSize)
        poke ptr a
        return (ArrayList 0 1 initialSize ptr)
    | len < half bufLen -> do
        moveArray ptr (advancePtr ptr start) len
        poke (advancePtr ptr len) a
        return (ArrayList 0 (len + 1) bufLen ptr)
    | otherwise -> do
        newPtr <- FMA.mallocBytes (FS.sizeOf (undefined :: a) * bufLen * 2)
        moveArray newPtr (advancePtr ptr start) len
        FMA.free ptr
        poke (advancePtr newPtr len) a
        return (ArrayList 0 (len + 1) (bufLen * 2) newPtr)

{-# INLINE pushArrayR #-}
pushArrayR :: forall a. (Storable a, Prim a) => ArrayList a -> PrimArray a -> IO (ArrayList a)
pushArrayR (ArrayList start len bufLen ptr) as =
  -- I think this should actually be less than or equal to
  if start + len + asLen < bufLen
    then do
      copyPrimArrayToPtr (advancePtr ptr (start + len)) as 0 asLen
      return (ArrayList start (len + asLen) bufLen ptr)
    else if
      -- this might give poor guarentees concerning worst
      -- case behaviors, but whatever for now.
      | len == 0 -> do
          when (bufLen /= 0) (fail "ArrayList.pushArrayR: invariant violated")
          when (start /= 0) (fail "ArrayList.pushArrayR: invariant violated")
          when (ptr /= nullPtr) (fail "ArrayList.pushArrayR: invariant violated")
          let newBufLen = twiceUntilExceeds initialSize asLen
          ptr <- FMA.mallocBytes (FS.sizeOf (undefined :: a) * newBufLen)
          copyPrimArrayToPtr ptr as 0 asLen
          return (ArrayList 0 asLen newBufLen ptr)
      | len < half bufLen && asLen < half bufLen -> do
          moveArray ptr (advancePtr ptr start) len
          copyPrimArrayToPtr (advancePtr ptr len) as 0 asLen
          return (ArrayList 0 (len + asLen) bufLen ptr)
      | otherwise -> do
          let newBufLen = twiceUntilExceeds (2 * bufLen) (len + asLen)
          newPtr <- FMA.mallocBytes (FS.sizeOf (undefined :: a) * newBufLen)
          moveArray newPtr (advancePtr ptr start) len
          FMA.free ptr
          copyPrimArrayToPtr (advancePtr newPtr len) as 0 asLen
          return (ArrayList 0 (len + asLen) newBufLen newPtr)
  where
  asLen = sizeofPrimArray as

twiceUntilExceeds :: Int -> Int -> Int
twiceUntilExceeds !i !limit = go i where 
  go !n = if n > limit
    then n
    else go (n * 2)
 

popL :: forall a. Storable a => ArrayList a -> IO (ArrayList a, Maybe a)
popL xs@(ArrayList start len bufLen ptr)
  | len < 1 = return (xs, Nothing)
  | otherwise = do
      a <- peek (advancePtr ptr start)
      newArrList <- minimizeMemory (ArrayList (start + 1) (len - 1) bufLen ptr)
      return (newArrList, Just a)

{-# INLINE dropWhileL #-}
dropWhileL :: forall a. Storable a
  => ArrayList a
  -> (a -> IO Bool) -- ^ predicate
  -> IO (ArrayList a,Int)
dropWhileL (ArrayList start len bufLen ptr) p = do
  let go :: Int -> IO Int
      go !i = if i < len
        then do
          a <- peek (advancePtr ptr (start + i))
          b <- p a
          if b
            then go (i + 1)
            else return i
        else return i
  dropped <- go 0
  newArrList <- minimizeMemory $ ArrayList (start + dropped) (len - dropped) bufLen ptr
  return (newArrList,dropped)

{-# INLINE dropWhileScanL #-}
dropWhileScanL :: forall a b. Storable a
  => ArrayList a
  -> b
  -> (b -> a -> IO (Bool,b))
  -> IO (ArrayList a,Int,b)
dropWhileScanL (ArrayList start len bufLen ptr) b0 p = do
  let go :: Int -> b -> IO (Int,b)
      go !i !b = if i < len
        then do
          !a <- peek (advancePtr ptr (start + i))
          (!shouldContinue,!b') <- p b a
          if shouldContinue
            then go (i + 1) b'
            else return (i,b')
        else return (i,b)
  (dropped,b') <- go 0 b0
  newArrList <- minimizeMemory $ ArrayList (start + dropped) (len - dropped) bufLen ptr
  return (newArrList,dropped,b')

{-# INLINE dropScanL #-}
dropScanL :: forall a b. Storable a
  => ArrayList a
  -> Int
  -> b
  -> (b -> a -> IO b)
  -> IO (ArrayList a, b)
dropScanL (ArrayList start len bufLen ptr) n b0 p = do
  let !m = min n len
  let go :: Int -> b -> IO b
      go !i !b = if i < m
        then do
          a <- peek (advancePtr ptr (start + i))
          b' <- p b a
          go (i + 1) b'
        else return b
  b' <- go 0 b0
  newArrList <- minimizeMemory $ ArrayList (start + m) (len - m) bufLen ptr
  return (newArrList,b')

{-# INLINE dropL #-}
dropL :: forall a. Storable a => ArrayList a -> Int -> IO (ArrayList a)
dropL (ArrayList start len bufLen ptr) n = do
  let m = min n len
  minimizeMemory $ ArrayList (start + m) (len - m) bufLen ptr

{-# INLINE minimizeMemory #-}
minimizeMemory :: forall a. Storable a => ArrayList a -> IO (ArrayList a)
minimizeMemory xs@(ArrayList start len bufLen ptr)
    -- We do not drop below a certain size, since then we would
    -- end up doing frequent reallocations. Although, once the size
    -- reaches zero, we deallocate entirely since this can save a lot
    -- of memory when we have many empty ArrayLists.
  | len == 0 = do
      FMA.free ptr
      return (ArrayList 0 0 0 nullPtr)
  | bufLen <= initialSize = return xs
  | len < eighth bufLen = do
      newPtr <- FMA.mallocBytes (FS.sizeOf (undefined :: a) * div bufLen 2)
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

{-# INLINE eighth #-}
eighth :: Int -> Int
eighth x = unsafeShiftR x 3

{-# INLINE sixteenth #-}
sixteenth :: Int -> Int
sixteenth x = unsafeShiftR x 4

-- | This should not be used in production code.
dumpList :: (Prim a, Storable a) => ArrayList a -> IO (ArrayList a, [a])
dumpList xs@(ArrayList _ len _ _) = do
  marr <- newPrimArray len
  newXs <- dump xs marr 0
  arr <- unsafeFreezePrimArray marr
  return (newXs,primArrayToList len arr)

-- | Deletes all elements from the linked list, copying them
--   into the buffer specified by the pointer. Returns an
--   empty linked list.
dump :: (Prim a, Storable a)
  => ArrayList a -> MutablePrimArray RealWorld a -> Int -> IO (ArrayList a)
dump xs@(ArrayList start len _ ptr) marr ix = do
  copyPtrToMutablePrimArray marr ix (advancePtr ptr start) len
  clear xs

-- | Dump the elements into a 'MutablePrimArray', mapping over them
--   first. This is a fairly niche function.
dumpMap :: (Storable a, Prim b)
  => ArrayList a -> (a -> b) -> MutablePrimArray RealWorld b -> Int -> IO (ArrayList a)
dumpMap xs@(ArrayList start len _ ptr) f marr ix = do
  let go :: Int -> IO ()
      go !i = if i < len
        then do
          a <- peekElemOff ptr (start + i)
          writePrimArray marr (ix + i) (f a)
        else return ()
  go 0
  clear xs

-- | Does not affect the contents of the ArrayList
showDebug :: forall a. (Prim a, Storable a, Show a) => ArrayList a -> IO String
showDebug (ArrayList start len _ ptr) = do
  marr <- newPrimArray len
  copyPtrToMutablePrimArray marr 0 (plusPtr ptr (start * PM.sizeOf (undefined :: a))) len
  arr <- unsafeFreezePrimArray marr
  return (show (primArrayToList len arr :: [a]))

clear :: Storable a => ArrayList a -> IO (ArrayList a)
clear xs@(ArrayList _ len _ _) = dropL xs len

-- | Final consumer of the ArrayList.
free :: ArrayList a -> IO ()
free (ArrayList _ _ _ ptr) = FMA.free ptr
  
