{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module BTree.Store
  ( BTree
  , new
  , free
  , with
  , lookup
  , insert
  , modifyWithM
  , foldrWithKey
  , toAscList
  ) where

import Prelude hiding (lookup)
import Foreign.Storable
import Foreign.Ptr
import Foreign.Marshal.Alloc hiding (free)
import Foreign.Marshal.Array
import Data.Bits
import Control.Exception (bracket)
import qualified Foreign.Marshal.Alloc as FMA

data BTree k v = BTree 
  !Int -- ^ height
  !(Ptr (Node k v)) -- ^ root node

data Node k v

class Storable a => Allocator a where
  initialize :: Ptr a -> IO ()
  -- ^ Initialize the memory at a pointer. An implementation
  --   of this function may do nothing, or if the data contains
  --   more pointers, @initialize@ may allocate additional memory.
  deinitialize :: Ptr a -> IO ()
  -- ^ Free any memory in the data structure pointed to.
  initializeElems :: Ptr a -> Int -> IO ()
  -- ^ Initialize a pointer representing an array with
  --   a given number of elements. This has a default implementation
  --   but may be overriden for efficency.
  initializeElems ptr n = go 0
    where
    go !i = if i < n
      then do
        initialize (plusPtr ptr (i * sizeOf (undefined :: a)) :: Ptr a)
        go (i + 1)
      else return ()

  deinitializeElems :: Ptr a -> Int -> IO ()
  -- ^ Free any memory pointed to by elements of the array.
  --   This has a default implementation
  --   but may be overriden for efficency.
  deinitializeElems ptr n = go 0
    where
    go !i = if i < n
      then do
        deinitialize (plusPtr ptr (i * sizeOf (undefined :: a)) :: Ptr a)
        go (i + 1)
      else return ()

instance Storable (BTree k v) where
  

-- this instance relies on Int and Ptr being the same
-- size. this seems to be true for everything that
-- GHC targets.
instance (Storable k, Storable v) => Allocator (BTree k v) where
  initialize ptr = do
    pokeElemOff (castPtr ptr :: Ptr Int) 0 (0 :: Int)
    pokeElemOff (castPtr ptr :: Ptr (Ptr (Node k v))) 1 =<< newNode 0
  deinitialize ptr = do
    bt <- peek ptr
    free bt


newtype Arr a = Arr { getArr :: Ptr a }
data KeysValues k v = KeysValues !(Arr k) !(Arr v)
data KeysNodes k v = KeysNodes !(Arr k) !(Arr (Ptr (Node k v)))

new :: forall k v. (Storable k, Storable v) => IO (BTree k v)
new = do
  -- we only calculate these degrees so that we can do one
  -- upfront check instead of check every time we call insert,
  -- which would be weird. This also helps us see the failure
  -- sooner.
  let childDegree = calcChildDegree (undefined :: Ptr (Node k v))
      branchDegree = calcBranchDegree (undefined :: Ptr (Node k v))
  if childDegree < 3
    then fail "Btree.new: child degree cannot be less than 3"
    else return ()
  if branchDegree < 3
    then fail "Btree.new: branch degree cannot be less than 3"
    else return ()
  ptr <- newNode 0
  return (BTree 0 ptr)

-- | Release all memory allocated by the b-tree. Do not attempt
--   to use the b-tree after calling this.
free :: forall k v. (Storable k, Storable v) => BTree k v -> IO ()
free (BTree height root) = go height root
  where
  branchDegree :: Int
  !branchDegree = calcBranchDegree root
  go :: Int -> Ptr (Node k v) -> IO ()
  go n ptrNode = if n > 0
    then do
      sz <- readNodeSize ptrNode
      let KeysNodes _ nodes = readNodeKeysNodes branchDegree ptrNode
      arrMapM_ (go (n - 1)) (sz + 1) nodes
      FMA.free ptrNode
    else FMA.free ptrNode

with :: (Storable k, Storable v) => (BTree k v -> IO a) -> IO a
with = bracket new free

newNode :: forall k v. (Storable k, Storable v)
  => Int -- ^ initial size, if you pick something greater than 0,
         --   you need to write to those indices after calling this.
  -> IO (Ptr (Node k v))
newNode n = do
  -- We would really like to ensure that this is aligned to a
  -- 4k boundary, but malloc does not guarentee this. I think
  -- that posix_memalign should work, but whatever.
  ptr <- mallocBytes 4096
  poke ptr n
  return (castPtr ptr)
  

readArr :: Storable a => Arr a -> Int -> IO a
readArr (Arr ptr) ix = peekElemOff ptr ix

writeArr :: Storable a => Arr a -> Int -> a -> IO ()
writeArr (Arr ptr) ix a = pokeElemOff ptr ix a

readNodeSize :: Ptr (Node k v) -> IO Int
readNodeSize ptr = peek (castPtr ptr)

writeNodeSize :: Ptr (Node k v) -> Int -> IO ()
writeNodeSize ptr sz = poke (castPtr ptr) sz

readNodeKeys :: forall k v. Storable k => Ptr (Node k v) -> Arr k
readNodeKeys ptr1 =
  let ptr2 = plusPtr ptr1 (sizeOf (undefined :: Int))
      ptr3 = alignPtr ptr2 (alignment (undefined :: k))
   in Arr ptr3

readNodeKeysValues :: forall k v. Storable k => Int -> Ptr (Node k v) -> KeysValues k v
readNodeKeysValues degree ptr1 = 
  let keys = readNodeKeys ptr1
      ptr2 = plusPtr (getArr keys) (sizeOf (undefined :: k) * (degree - 1))
      ptr3 = alignPtr ptr2 (alignment (undefined :: k))
   in KeysValues keys (Arr ptr3)

readNodeKeysNodes :: forall k v. Storable k => Int -> Ptr (Node k v) -> KeysNodes k v
readNodeKeysNodes degree ptr1 = 
  let keys = readNodeKeys ptr1
      ptr2 = plusPtr (getArr keys) (sizeOf (undefined :: k) * (degree - 1))
      ptr3 = alignPtr ptr2 (alignment (undefined :: (Ptr (Node k v))))
   in KeysNodes keys (Arr ptr3)

maxSize :: Int
maxSize = 4096

-- not actually sure if this is really correct.
calcBranchDegree :: forall k v. (Storable k, Storable v) => Ptr (Node k v) -> Int
calcBranchDegree _ = 
  let space = maxSize - max (sizeOf (undefined :: Int)) (alignment (undefined :: k)) - sizeOf (undefined :: Ptr (Node k v))
      allowedNodes = quot space (sizeOf (undefined :: Ptr (Node k v)) + sizeOf (undefined :: k))
   in allowedNodes

-- not actually sure if this is really correct. need to think about this math
-- a little more. Or I guess I could write something that does a brute force
-- consideration of all the possible sizes and alignment. That would convince me.
calcChildDegree :: forall k v. (Storable k, Storable v) => Ptr (Node k v) -> Int
calcChildDegree _ = 
  let space = maxSize - max (sizeOf (undefined :: Int)) (alignment (undefined :: k)) - sizeOf (undefined :: v)
      allowedValues = quot space (sizeOf (undefined :: v) + sizeOf (undefined :: k))
   in allowedValues + 1 -- add one because of the meaning we assign to degree

lookup :: forall k v. (Ord k, Storable k, Storable v)
  => BTree k v -> k -> IO (Maybe v)
lookup (BTree height rootNode) k = go height rootNode
  where
  branchDegree :: Int
  !branchDegree = calcBranchDegree rootNode
  childDegree :: Int
  childDegree = calcChildDegree rootNode
  go :: Int -> Ptr (Node k v) -> IO (Maybe v)
  go n ptrNode = if n > 0
    then do
      sz <- readNodeSize ptrNode
      let KeysNodes keys nodes = readNodeKeysNodes branchDegree ptrNode
      ix <- findIndexOfGtElem keys k sz
      !node <- readArr nodes ix
      go (n - 1) node
    else do
      sz <- readNodeSize ptrNode
      let KeysValues keys values = readNodeKeysValues childDegree ptrNode
      ix <- findIndex keys k sz
      if ix < 0
        then return Nothing
        else do
          v <- readArr values ix
          return (Just v)

data Decision a = Keep | Replace !a

data Insert k v
  = Ok !v
  | Split {-# NOUNPACK #-} !(Ptr (Node k v)) !k !v
    -- The new node that will go to the right,
    -- the key propagated to the parent,
    -- the inserted value

{-# INLINE insert #-}
insert :: (Ord k, Storable k, Storable v)
  => BTree k v
  -> k
  -> v
  -> IO (BTree k v)
insert !m !k !v = do
  !(!_,!node) <- modifyWithM m k v (\_ -> return (Replace v))
  return node

modifyWithM :: forall k v. (Ord k, Storable k, Storable v)
  => BTree k v 
  -> k
  -> v -- ^ value to insert if key not found
  -> (v -> IO (Decision v)) -- ^ modification to value if key is found
  -> IO (v, BTree k v)
modifyWithM (BTree !height !root) !k !newValue alter = do
  !ins <- go height root
  case ins of
    Ok !v -> return (v,BTree height root)
    Split !rightNode !newRootKey !v -> do
      newRoot <- newNode 1
      let KeysNodes keys nodes = readNodeKeysNodes branchDegree newRoot
          leftNode = root
      writeArr keys 0 newRootKey
      writeArr nodes 0 leftNode
      writeArr nodes 1 rightNode
      return (v,BTree (height + 1) newRoot)
  where
  branchDegree :: Int
  !branchDegree = calcBranchDegree root
  go :: Int -> Ptr (Node k v) -> IO (Insert k v)
  go n ptrNode = if n > 0
    then do
      sz <- readNodeSize ptrNode
      let KeysNodes keys nodes = readNodeKeysNodes branchDegree ptrNode
      !gtIx <- findIndexOfGtElem keys k sz
      !node <- readArr nodes gtIx
      !ins <- go (n - 1) node
      case ins of
        Ok !v -> return (Ok v)
        Split !rightNode !propagated !v -> if sz < branchDegree - 1
          then do
            insertArr sz gtIx propagated keys
            insertArr (sz + 1) (gtIx + 1) rightNode nodes
            writeNodeSize ptrNode (sz + 1)
            return (Ok v)
          else do
            let !middleIx = half sz
                !leftKeys = keys
                !leftNodes = nodes
            !middleKey <- readArr keys middleIx
            let !leftSize = middleIx
                !rightSize = sz - leftSize
                (!actualLeftSz,!actualRightSz) = if middleIx >= gtIx
                  then (leftSize + 1, rightSize - 1)
                  else (leftSize, rightSize)
            newNodePtr <- newNode actualRightSz
            writeNodeSize ptrNode actualLeftSz
            let KeysNodes rightKeys rightNodes = readNodeKeysNodes branchDegree newNodePtr
            if middleIx >= gtIx
              then do
                copyArr rightKeys 0 leftKeys (leftSize + 1) (rightSize - 1)
                copyArr rightNodes 0 leftNodes (leftSize + 1) rightSize
                insertArr leftSize gtIx propagated leftKeys
                insertArr (leftSize + 1) (gtIx + 1) rightNode leftNodes
              else do
                -- Currently, we're copying from left to right and
                -- then doing another copy from right to right. We can do better.
                copyArr rightKeys 0 leftKeys (leftSize + 1) (rightSize - 1)
                copyArr rightNodes 0 leftNodes (leftSize + 1) rightSize
                insertArr (rightSize - 1) (gtIx - leftSize - 1) propagated rightKeys
                insertArr rightSize (gtIx - leftSize) rightNode rightNodes
            return (Split newNodePtr middleKey v)
    else do
      sz <- readNodeSize ptrNode
      let childDegree = calcChildDegree root
          KeysValues keys values = readNodeKeysValues childDegree ptrNode
      !ix <- findIndex keys k sz
      if ix < 0
        then do
          let !gtIx = decodeGtIndex ix
              !v = newValue
          if sz < childDegree - 1
            then do
              -- We have enough space
              writeNodeSize ptrNode (sz + 1)
              insertArr sz gtIx k keys
              insertArr sz gtIx v values
              return (Ok v)
            else do
              -- We do not have enough space. The node must be split.
              let !leftSize = half sz
                  !rightSize = sz - leftSize
                  !leftKeys = keys
                  !leftValues = values
              let (newLeftSz,actualRightSz) = if gtIx < leftSize
                    then (leftSize + 1, rightSize)
                    else (leftSize,rightSize + 1)
              newNodePtr <- newNode actualRightSz
              writeNodeSize ptrNode newLeftSz
              let KeysValues rightKeys rightValues = readNodeKeysValues childDegree newNodePtr
              if gtIx < leftSize
                then do
                  copyArr rightKeys 0 leftKeys leftSize rightSize
                  copyArr rightValues 0 leftValues leftSize rightSize
                  insertArr leftSize gtIx k leftKeys
                  insertArr leftSize gtIx v leftValues
                else do
                  -- Currently, we're copying from left to right and
                  -- then doing another copy from right to right. We
                  -- might be able to do better. We could do the same number
                  -- of memcpys but copy fewer total elements and not
                  -- have the slowdown caused by overlap.
                  copyArr rightKeys 0 leftKeys leftSize rightSize
                  copyArr rightValues 0 leftValues leftSize rightSize
                  insertArr rightSize (gtIx - leftSize) k rightKeys
                  insertArr rightSize (gtIx - leftSize) v rightValues
              !propagated <- readArr rightKeys 0
              return (Split newNodePtr propagated v)
        else do
          !v <- readArr values ix
          !dec <- alter v
          !v' <- case dec of
            Keep -> return v
            Replace v' -> writeArr values ix v' >> return v'
          return (Ok v')

copyArr :: forall a. Storable a
  => Arr a -- ^ dest
  -> Int -- ^ dest offset
  -> Arr a -- ^ source
  -> Int -- ^ source offset
  -> Int -- ^ length
  -> IO ()
copyArr (Arr dest) doff (Arr src) soff len = moveArray
  (advancePtr dest doff)
  (advancePtr src soff)
  len

insertArr :: Storable a
  => Int -- ^ Size of the original array
  -> Int -- ^ Index
  -> a -- ^ Value
  -> Arr a -- ^ Array to modify
  -> IO ()
insertArr !sz !i !x !arr = do
  copyArr arr (i + 1) arr i (sz - i)
  writeArr arr i x

-- | This lookup is O(log n). It provides the index of the
--   first element greater than the argument.
--   Precondition, the array provided is sorted low to high.
{-# INLINABLE findIndexOfGtElem #-}
findIndexOfGtElem :: (Ord a, Storable a) => Arr a -> a -> Int -> IO Int
findIndexOfGtElem v needle sz = go 0 (sz - 1)
  where
  go :: Int -> Int -> IO Int
  go !lo !hi = if lo <= hi
    then do
      let !mid = lo + half (hi - lo)
      !val <- readArr v mid
      if | val == needle -> return (mid + 1)
         | val < needle -> go (mid + 1) hi
         | otherwise -> go lo (mid - 1)
    else return lo

-- Preconditions:
-- * marr is sorted low to high
-- * sz is less than or equal to the true size of marr
-- The returned value is either
-- * in the inclusive range [0,sz - 1], indicates a match
-- * a negative number x, indicates that the first greater
--   element is found at index ((negate x) - 1)
findIndex :: (Ord a, Storable a)
  => Arr a
  -> a
  -> Int
  -> IO Int -- (Either Int Int)
findIndex !marr !needle !sz = go 0
  where
  go :: Int -> IO Int
  go !i = if i < sz
    then do
      !a <- readArr marr i
      case compare a needle of
        LT -> go (i + 1)
        EQ -> return i
        GT -> return (encodeGtIndex i)
    else return (encodeGtIndex i)

foldrWithKey :: forall k v b. (Ord k, Storable k, Storable v)
  => (k -> v -> b -> IO b)
  -> b
  -> BTree k v
  -> IO b
foldrWithKey f b0 (BTree height root) = go height root b0
  where
  branchDegree :: Int
  !branchDegree = calcBranchDegree root
  childDegree :: Int
  childDegree = calcChildDegree root
  go :: Int -> Ptr (Node k v) -> b -> IO b
  go !n !ptrNode b = do
    sz <- readNodeSize ptrNode
    if n > 0
      then do
        let KeysNodes _ nodes = readNodeKeysNodes branchDegree ptrNode
        foldrArray (sz + 1) (go (n - 1)) b nodes
      else do
        let KeysValues keys values = readNodeKeysValues childDegree ptrNode
        foldrPrimArrayPairs sz f b keys values

foldrPrimArrayPairs :: forall k v b. (Ord k, Storable k, Storable v)
  => Int -- ^ length of arrays
  -> (k -> v -> b -> IO b)
  -> b
  -> Arr k
  -> Arr v
  -> IO b
foldrPrimArrayPairs len f b0 ks vs = go (len - 1) b0
  where
  go :: Int -> b -> IO b
  go !ix !b1 = if ix >= 0
    then do
      k <- readArr ks ix
      v <- readArr vs ix
      b2 <- f k v b1
      go (ix - 1) b2
    else return b1

foldrArray :: forall a b. Storable a
  => Int -- ^ length of array
  -> (a -> b -> IO b)
  -> b
  -> Arr a
  -> IO b
foldrArray len f b0 arr = go (len - 1) b0
  where
  go :: Int -> b -> IO b
  go !ix !b1 = if ix >= 0
    then do
      a <- readArr arr ix
      b2 <- f a b1
      go (ix - 1) b2
    else return b1

arrMapM_ :: (Storable a) => (a -> IO b) -> Int -> Arr a -> IO ()
arrMapM_ f len arr = go 0
  where
  go :: Int -> IO ()
  go i = if i < len
    then do
      _ <- f =<< readArr arr i
      go (i + 1)
    else return ()
  

{-# INLINE encodeGtIndex #-}
encodeGtIndex :: Int -> Int
encodeGtIndex i = negate i - 1

{-# INLINE decodeGtIndex #-}
decodeGtIndex :: Int -> Int
decodeGtIndex x = negate x - 1

{-# INLINE half #-}
half :: Int -> Int
half x = unsafeShiftR x 1

-- | This is provided for convenience but is not something
--   typically useful in producetion code.
toAscList :: forall k v. (Ord k, Storable k, Storable v)
  => BTree k v
  -> IO [(k,v)]
toAscList = foldrWithKey f []
  where
  f :: k -> v -> [(k,v)] -> IO [(k,v)]
  f k v xs = return ((k,v) : xs)


