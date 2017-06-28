{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE Strict #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE UnboxedSums #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE DataKinds #-}

{-# OPTIONS_GHC -O2 -Wall -Werror -fno-warn-unused-imports #-}

module BTree.Compact
  ( BTree
  , Decision(..)
  , new
  , debugMap
  , insert
  , modifyWithM
  , lookup
  , toAscList
  , foldrWithKey
  ) where

import Prelude hiding (lookup)
import Data.Primitive hiding (fromList)
import Control.Monad
import Data.Foldable (foldlM)
import Data.Primitive.Compact
import Data.Word
import Control.Monad.ST
import Control.Monad.Primitive
import GHC.Prim
import Data.Bits (unsafeShiftR)

import Data.Primitive.PrimRef
import Data.Primitive.PrimArray
import Data.Primitive.MutVar
import GHC.Ptr (Ptr(..))
import GHC.Int (Int(..))
import Numeric (showHex)

import qualified Data.List as L

data BTree k v s (c :: Heap) = BTree
  {-# UNPACK #-} !Int -- degree
  {-# UNPACK #-} !(BNode k v s c)

-- Use mkBTree instead. Using this for pattern matching is ok. 
data BNode k v s (c :: Heap) = BNode
  { _bnodeSize :: {-# UNPACK #-} !Int -- size, number of keys present in node
  , _bnodeKeys :: {-# UNPACK #-} !(MutablePrimArray s k)
  , _bnodeContents :: {-# UNPACK #-} !(FlattenedContents k v s c)
  }

-- In defining this instance, we make the assumption that an
-- Addr and an Int have the same size.
instance Contractible (BNode k v) where
  unsafeContractedUnliftedPtrCount# _ = 4#
  unsafeContractedByteCount# _ = sizeOf# (undefined :: Int) *# 2#
  readContractedArray# ba aa ix s1 =
    let ixByte = ix *# 2#
        ixPtr = ix *# 4#
     in case readIntArray# ba (ixByte +# 0#) s1 of
         (# s2, sz #) -> case readIntArray# ba (ixByte +# 1#) s2 of
          (# s3, toggle #) -> case readMutableByteArrayArray# aa (ixPtr +# 0#) s3 of
           (# s4, keys #) -> case readMutableByteArrayArray# aa (ixPtr +# 1#) s4 of
            (# s5, values #) -> case readMutableByteArrayArray# aa (ixPtr +# 2#) s5 of
             (# s6, nodesBytes #) -> case readMutableArrayArrayArray# aa (ixPtr +# 3#) s6 of
              (# s7, nodesPtrs #) ->
               (# s7, (BNode (I# sz) (MutablePrimArray keys) (FlattenedContents (I# toggle) (MutablePrimArray values) (ContractedMutableArray nodesBytes nodesPtrs))) #)
  writeContractedArray# ba aa ix (BNode (I# sz) (MutablePrimArray keys) (FlattenedContents (I# toggle) (MutablePrimArray values) (ContractedMutableArray nodesBytes nodesPtrs))) s1 =
    let ixByte = ix *# 2#
        ixPtr = ix *# 4#
     in case writeIntArray# ba (ixByte +# 0#) sz s1 of
         s2 -> case writeIntArray# ba (ixByte +# 1#) toggle s2 of
          s3 -> case writeMutableByteArrayArray# aa (ixPtr +# 0#) keys s3 of
           s4 -> case writeMutableByteArrayArray# aa (ixPtr +# 1#) values s4 of
            s5 -> case writeMutableByteArrayArray# aa (ixPtr +# 2#) nodesBytes s5 of
             s6 -> writeMutableArrayArrayArray# aa (ixPtr +# 3#) nodesPtrs s6

instance Contractible (BTree k v) where
  unsafeContractedUnliftedPtrCount# _ = 4#
  unsafeContractedByteCount# _ = sizeOf# (undefined :: Int) *# 3#
  readContractedArray# ba aa ix s1 =
    let ixByte = ix *# 3#
        ixPtr = ix *# 4#
     in case readIntArray# ba (ixByte +# 0#) s1 of
         (# s2, sz #) -> case readIntArray# ba (ixByte +# 1#) s2 of
          (# s3, toggle #) -> case readIntArray# ba (ixByte +# 2#) s3 of
           (# s4, degree #) -> case readMutableByteArrayArray# aa (ixPtr +# 0#) s4 of
            (# s5, keys #) -> case readMutableByteArrayArray# aa (ixPtr +# 1#) s5 of
             (# s6, values #) -> case readMutableByteArrayArray# aa (ixPtr +# 2#) s6 of
              (# s7, nodesBytes #) -> case readMutableArrayArrayArray# aa (ixPtr +# 3#) s7 of
               (# s8, nodesPtrs #) ->
                (# s8, BTree (I# degree) (BNode (I# sz) (MutablePrimArray keys) (FlattenedContents (I# toggle) (MutablePrimArray values) (ContractedMutableArray nodesBytes nodesPtrs))) #)
  writeContractedArray# ba aa ix (BTree (I# degree) (BNode (I# sz) (MutablePrimArray keys) (FlattenedContents (I# toggle) (MutablePrimArray values) (ContractedMutableArray nodesBytes nodesPtrs)))) s1 =
    let ixByte = ix *# 3#
        ixPtr = ix *# 4#
     in case writeIntArray# ba (ixByte +# 0#) sz s1 of
         s2 -> case writeIntArray# ba (ixByte +# 1#) toggle s2 of
          s3 -> case writeIntArray# ba (ixByte +# 2#) degree s3 of
           s4 -> case writeMutableByteArrayArray# aa (ixPtr +# 0#) keys s4 of
            s5 -> case writeMutableByteArrayArray# aa (ixPtr +# 1#) values s5 of
             s6 -> case writeMutableByteArrayArray# aa (ixPtr +# 2#) nodesBytes s6 of
              s7 -> writeMutableArrayArrayArray# aa (ixPtr +# 3#) nodesPtrs s7
   
-- We manually flatten this sum type so that it can be unpacked
-- into BNode.
data FlattenedContents k v s c = FlattenedContents
  {-# UNPACK #-} !Int
  {-# UNPACK #-} !(MutablePrimArray s v)
  {-# UNPACK #-} !(ContractedMutableArray (BNode k v) s c)

data Contents k v s c
  = ContentsValues {-# UNPACK #-} !(MutablePrimArray s v)
  | ContentsNodes {-# UNPACK #-} !(ContractedMutableArray (BNode k v) s c)

{-# INLINE flattenContentsToContents #-}
flattenContentsToContents :: 
     FlattenedContents k v s c
  -> Contents k v s c
flattenContentsToContents (FlattenedContents i values nodes) =
  if i == 0
    then ContentsValues values
    else ContentsNodes nodes

-- | This one is a little trickier. We have to provide garbage
--   to fill in the unused slot.
{-# INLINE contentsToFlattenContents #-}
contentsToFlattenContents :: 
     MutablePrimArray s v -- ^ garbage value
  -> ContractedMutableArray (BNode k v) s c -- ^ garbage value
  -> Contents k v s c
  -> FlattenedContents k v s c
contentsToFlattenContents !garbageValues !garbageNodes !c = case c of
  ContentsValues values -> FlattenedContents 0 values garbageNodes
  ContentsNodes nodes -> FlattenedContents 1 garbageValues nodes 

-- | Get the nodes out, even if they are garbage. This is used
--   to get a garbage value when needed.
{-# INLINE demandFlattenedContentsNodes #-}
demandFlattenedContentsNodes :: FlattenedContents k v s c -> ContractedMutableArray (BNode k v) s c
demandFlattenedContentsNodes (FlattenedContents _ _ nodes) = nodes

data Insert k v s c
  = Ok
      !v
      {-# UNPACK #-} !Int -- new size of left child
  | Split
      {-# NOUNPACK #-} !(BNode k v s c)
      !k
      !v
      {-# UNPACK #-} !Int
      -- ^ The new node that will go to the right,
      --   the key propagated to the parent,
      --   the inserted value, updated sizing info for the left child

{-# INLINE mkBTree #-}
mkBTree :: PrimMonad m
  => Token c
  -> ContractedMutableArray (BNode k v) (PrimState m) c -- ^ garbage value
  -> Int -- Sizing (PrimState m) c
  -> MutablePrimArray (PrimState m) k -- ^ keys
  -> Contents k v (PrimState m) c
  -> m (BNode k v (PrimState m) c)
mkBTree token garbage a b c = do
  let !garbageValues = coercePrimArray b
      !bt = BNode a b (contentsToFlattenContents garbageValues garbage c)
  compactAddGeneral token bt

coercePrimArray :: MutablePrimArray s a -> MutablePrimArray s b
coercePrimArray (MutablePrimArray a) = MutablePrimArray a

new :: (PrimMonad m, Prim k, Prim v)
  => Token c
  -> Int -- ^ degree, must be at least 3
  -> m (BTree k v (PrimState m) c)
new !token !degree = do
  if degree < 3
    then error "Btree.new: max nodes per child cannot be less than 3"
    else return ()
  !keys <- newPrimArray (degree - 1)
  !values <- newPrimArray (degree - 1)
  -- it kind of pains me that this is needed, but since
  -- we only do it once when calling @new@, it should
  -- not hurt performance at all.
  !garbageNodes <- newContractedArray token 0
  node <- mkBTree token garbageNodes 0 keys (ContentsValues values)
  return (BTree degree node)

-- {-# SPECIALIZE lookup :: BNode RealWorld Int Int c -> Int -> IO (Maybe Int) #-}
{-# INLINABLE lookup #-}
lookup :: forall m k v c. (PrimMonad m, Ord k, Prim k, Prim v)
  => BTree k v (PrimState m) c -> k -> m (Maybe v)
lookup (BTree _ theNode) k = go theNode
  where
  go :: BNode k v (PrimState m) c -> m (Maybe v)
  go (BNode sz keys c@(FlattenedContents _tog _ _)) = do
    case flattenContentsToContents c of
      ContentsValues values -> do
        ix <- findIndex keys k sz
        if ix < 0
          then return Nothing
          else do
            v <- readPrimArray values ix
            return (Just v)
      ContentsNodes nodes -> do
        ix <- findIndexOfGtElem keys k sz
        !node <- readContractedArray nodes ix
        go node

{-# INLINE insert #-}
insert :: (Ord k, Prim k, Prim v, PrimMonad m)
  => Token c
  -> BTree k v (PrimState m) c
  -> k
  -> v
  -> m (BTree k v (PrimState m) c)
insert !token !m !k !v = do
  !(!_,!node) <- modifyWithM token m k v (\_ -> return (Replace v))
  return node

data Decision a = Keep | Replace !a

-- When we turn on this specialize pragma, it gets way faster
-- for the particular case.
{-# SPECIALIZE modifyWithM :: Token c -> BTree Int Int RealWorld c -> Int -> Int -> (Int -> IO (Decision Int)) -> IO (Int, BTree Int Int RealWorld c) #-}
{-# INLINABLE modifyWithM #-}
modifyWithM :: forall m k v c. (Ord k, Prim k, Prim v, PrimMonad m)
  => Token c
  -> BTree k v (PrimState m) c
  -> k
  -> v -- ^ value to insert if key not found
  -> (v -> m (Decision v)) -- ^ modification to value if key is found
  -> m (v, BTree k v (PrimState m) c)
modifyWithM !token (BTree !degree !root) !k !newValue alter = do
  !ins <- go root
  case ins of
    Ok !v !newNodeSz -> return (v,BTree degree (root { _bnodeSize = newNodeSz }))
    Split !rightNode !newRootKey !v !newLeftSize -> do
      newRootKeys <- newPrimArray (degree - 1)
      writePrimArray newRootKeys 0 newRootKey
      !newRootChildren <- newContractedArray token degree
      let !leftNode = root { _bnodeSize = newLeftSize }
      !newRoot@(BNode _ _ (FlattenedContents _ _ cmptRootChildren)) <- mkBTree token newRootChildren 1 newRootKeys (ContentsNodes newRootChildren)
      writeContractedArray cmptRootChildren 0 leftNode
      writeContractedArray cmptRootChildren 1 rightNode
      return (v,BTree degree newRoot)
  where
  go :: BNode k v (PrimState m) c -> m (Insert k v (PrimState m) c)
  go (BNode !sz !keys !c) = do
    case flattenContentsToContents c of
      ContentsValues !values -> do
        !ix <- findIndex keys k sz
        if ix < 0
          then do
            let !gtIx = decodeGtIndex ix
                !v = newValue
            if sz < degree - 1
              then do
                -- We have enough space
                unsafeInsertPrimArray sz gtIx k keys
                unsafeInsertPrimArray sz gtIx v values
                return (Ok v (sz + 1))
              else do
                -- We do not have enough space. The node must be split.
                let !leftSize = div sz 2
                    !rightSize = sz - leftSize
                    !leftKeys = keys
                    !leftValues = values
                rightKeys' <- newPrimArray (degree - 1)
                rightValues' <- newPrimArray (degree - 1)
                let (newLeftSz,actualRightSz) = if gtIx < leftSize
                      then (leftSize + 1, rightSize)
                      else (leftSize,rightSize + 1)
                !newTree@(BNode _ rightKeys (FlattenedContents _ rightValues _)) <- mkBTree token (demandFlattenedContentsNodes c) actualRightSz rightKeys' (ContentsValues rightValues')
                if gtIx < leftSize
                  then do
                    copyMutablePrimArray rightKeys 0 leftKeys leftSize rightSize
                    copyMutablePrimArray rightValues 0 leftValues leftSize rightSize
                    unsafeInsertPrimArray leftSize gtIx k leftKeys
                    unsafeInsertPrimArray leftSize gtIx v leftValues
                  else do
                    -- Currently, we're copying from left to right and
                    -- then doing another copy from right to right. We
                    -- might be able to do better. We could do the same number
                    -- of memcpys but copy fewer total elements and not
                    -- have the slowdown caused by overlap.
                    copyMutablePrimArray rightKeys 0 leftKeys leftSize rightSize
                    copyMutablePrimArray rightValues 0 leftValues leftSize rightSize
                    unsafeInsertPrimArray rightSize (gtIx - leftSize) k rightKeys
                    unsafeInsertPrimArray rightSize (gtIx - leftSize) v rightValues
                !propagated <- readPrimArray rightKeys 0
                return (Split newTree propagated v newLeftSz)
          else do
            !v <- readPrimArray values ix
            !dec <- alter v
            !v' <- case dec of
              Keep -> return v
              Replace v' -> writePrimArray values ix v' >> return v'
            return (Ok v' sz)
      ContentsNodes nodes -> do
        !(!gtIx,!isEq) <- findIndexGte keys k sz
        -- case e of
        --   Right _ -> error "write Right case"
        --   Left gtIx -> do
        let !nodeIx = if isEq then gtIx + 1 else gtIx
        !node <- readContractedArray nodes nodeIx
        !ins <- go node
        case ins of
          Ok !v !newNodeSz -> do
            when (newNodeSz /= _bnodeSize node) $ do
              writeContractedArray nodes nodeIx (node { _bnodeSize = newNodeSz })
            return (Ok v sz)
          Split !rightNode !propagated !v !newNodeSz -> do
            when (newNodeSz /= _bnodeSize node) $ do
              writeContractedArray nodes nodeIx (node { _bnodeSize = newNodeSz })
            if sz < degree - 1
              then do
                unsafeInsertPrimArray sz gtIx propagated keys
                unsafeInsertContractedArray (sz + 1) (gtIx + 1) rightNode nodes
                -- writeNodeSize szRef (sz + 1)
                -- writeMutVar sizingRef sizing
                return (Ok v (sz + 1))
              else do
                let !middleIx = div sz 2
                    !leftKeys = keys
                    !leftNodes = nodes
                !middleKey <- readPrimArray keys middleIx
                !rightKeysOnHeap <- newPrimArray (degree - 1)
                !rightNodes' <- newContractedArray token degree -- uninitializedNode
                let !leftSize = middleIx
                    !rightSize = sz - leftSize
                    (!actualLeftSz,!actualRightSz) = if middleIx >= gtIx
                      then (leftSize + 1, rightSize - 1)
                      else (leftSize, rightSize)
                -- _ <- error ("die: " ++ show actualRightSz ++ " " ++ show sz ++ " " ++ show actualLeftSz)
                !x@(BNode _ rightKeys (FlattenedContents _ _ rightNodes)) <- mkBTree token rightNodes' actualRightSz rightKeysOnHeap (ContentsNodes rightNodes')
                if middleIx >= gtIx
                  then do
                    copyMutablePrimArray rightKeys 0 leftKeys (leftSize + 1) (rightSize - 1)
                    copyContractedMutableArray rightNodes 0 leftNodes (leftSize + 1) rightSize
                    unsafeInsertPrimArray leftSize gtIx propagated leftKeys
                    unsafeInsertContractedArray (leftSize + 1) (gtIx + 1) rightNode leftNodes
                  else do
                    -- Currently, we're copying from left to right and
                    -- then doing another copy from right to right. We can do better.
                    -- There is a similar note further up.
                    copyMutablePrimArray rightKeys 0 leftKeys (leftSize + 1) (rightSize - 1)
                    copyContractedMutableArray rightNodes 0 leftNodes (leftSize + 1) rightSize
                    unsafeInsertPrimArray (rightSize - 1) (gtIx - leftSize - 1) propagated rightKeys
                    unsafeInsertContractedArray rightSize (gtIx - leftSize) rightNode rightNodes
                return (Split x middleKey v actualLeftSz)

-- Preconditions:
-- * marr is sorted low to high
-- * sz is less than or equal to the true size of marr
-- The returned value is either
-- * in the inclusive range [0,sz - 1], indicates a match
-- * a negative number x, indicates that the first greater
--   element is found at index ((negate x) - 1)
findIndex :: forall m a. (PrimMonad m, Ord a, Prim a)
  => MutablePrimArray (PrimState m) a
  -> a
  -> Int
  -> m Int -- (Either Int Int)
findIndex !marr !needle !sz = go 0
  where
  go :: Int -> m Int
  go !i = if i < sz
    then do
      !a <- readPrimArray marr i
      case compare a needle of
        LT -> go (i + 1)
        EQ -> return i
        GT -> return (encodeGtIndex i)
    else return (encodeGtIndex i)

{-# INLINE encodeGtIndex #-}
encodeGtIndex :: Int -> Int
encodeGtIndex i = negate i - 1

{-# INLINE decodeGtIndex #-}
decodeGtIndex :: Int -> Int
decodeGtIndex x = negate x - 1

-- | The second value in the tuple is true when
--   the index match was exact.
findIndexGte :: forall m a. (Ord a, Prim a, PrimMonad m)
  => MutablePrimArray (PrimState m) a -> a -> Int -> m (Int,Bool)
findIndexGte !marr !needle !sz = go 0
  where
  go :: Int -> m (Int,Bool)
  go !i = if i < sz
    then do
      !a <- readPrimArray marr i
      case compare a needle of
        LT -> go (i + 1)
        EQ -> return (i,True)
        GT -> return (i,False)
    else return (i,False)

-- | This is a linear-cost search in an sorted array.
-- findIndexBetween :: forall m a. (PrimMonad m, Ord a, Prim a)
--   => MutablePrimArray (PrimState m) a -> a -> Int -> m Int
-- findIndexBetween !marr !needle !sz = go 0
--   where
--   go :: Int -> m Int
--   go !i = if i < sz
--     then do
--       a <- readPrimArray marr i
--       if a > needle
--         then return i
--         else go (i + 1)
--     else return i -- i should be equal to sz

-- Inserts a value at the designated index,
-- shifting everything after it to the right.
--
-- Example:
-- -----------------------------
-- | a | b | c | d | e | X | X |
-- -----------------------------
-- unsafeInsertPrimArray 5 3 'k' marr
--
unsafeInsertPrimArray ::
     (Prim a, PrimMonad m)
  => Int -- ^ Size of the original array
  -> Int -- ^ Index
  -> a -- ^ Value
  -> MutablePrimArray (PrimState m) a -- ^ Array to modify
  -> m ()
unsafeInsertPrimArray !sz !i !x !marr = do
  copyMutablePrimArray marr (i + 1) marr i (sz - i)
  writePrimArray marr i x

debugMap :: forall m k v c. (Prim k, Prim v, Show k, Show v, PrimMonad m)
  => BTree k v (PrimState m) c
  -> m String
debugMap (BTree _ (BNode !rootSz !rootKeys !rootContents)) = do
  let go :: Int -> Int -> MutablePrimArray (PrimState m) k -> FlattenedContents k v (PrimState m) c -> m [(Int,String)]
      go level sz keys c = case flattenContentsToContents c of
        ContentsValues values -> do
          pairStrs <- showPairs sz keys values
          return (map (\s -> (level,s)) pairStrs)
        ContentsNodes nodes -> do
          pairs <- pairForM sz keys nodes
            $ \k (BNode nextSz nextKeys nextContents) -> do
              nextStrs <- go (level + 1) nextSz nextKeys nextContents
              return (nextStrs ++ [(level,show k)]) -- ++ " (Size: " ++ show nextSz ++ ")")])
          -- I think this should always end up being in bounds
          BNode lastSz lastKeys lastContents <- readContractedArray nodes sz
          lastStrs <- go (level + 1) lastSz lastKeys lastContents
          -- return (nextStrs ++ [(level,show k)])
          return ([(level, "start")] ++ concat pairs ++ lastStrs)
  allStrs <- go 0 rootSz rootKeys rootContents
  return $ unlines $ map (\(level,str) -> replicate (level * 2) ' ' ++ str) ((0,"root size: " ++ show rootSz) : allStrs)

pairForM :: forall m a b c d. (Prim a, PrimMonad m, Contractible d)
  => Int 
  -> MutablePrimArray (PrimState m) a 
  -> ContractedMutableArray d (PrimState m) c
  -> (a -> d (PrimState m) c -> m b)
  -> m [b]
pairForM sz marr1 marr2 f = go 0
  where
  go :: Int -> m [b]
  go ix = if ix < sz
    then do
      a <- readPrimArray marr1 ix
      c <- readContractedArray marr2 ix
      b <- f a c
      bs <- go (ix + 1)
      return (b : bs)
    else return []

showPairs :: forall m k v. (PrimMonad m, Show k, Show v, Prim k, Prim v)
  => Int -- size
  -> MutablePrimArray (PrimState m) k
  -> MutablePrimArray (PrimState m) v
  -> m [String]
showPairs sz keys values = go 0
  where
  go :: Int -> m [String]
  go ix = if ix < sz
    then do
      k <- readPrimArray keys ix
      v <- readPrimArray values ix
      let str = show k ++ ": " ++ show v
      strs <- go (ix + 1)
      return (str : strs)
    else return []

-- | This is provided for completeness but is not something
--   typically useful in production code.
toAscList :: forall m k v c. (PrimMonad m, Ord k, Prim k, Prim v)
  => BTree k v (PrimState m) c
  -> m [(k,v)]
toAscList = foldrWithKey f []
  where
  f :: k -> v -> [(k,v)] -> m [(k,v)]
  f k v xs = return ((k,v) : xs)

foldrWithKey :: forall m k v b c. (PrimMonad m, Ord k, Prim k, Prim v)
  => (k -> v -> b -> m b)
  -> b
  -> BTree k v (PrimState m) c
  -> m b
foldrWithKey f b0 (BTree _ root) = flip go b0 root
  where
  go :: BNode k v (PrimState m) c -> b -> m b
  go (BNode sz keys c) !b = do
    case flattenContentsToContents c of
      ContentsValues values -> foldrPrimArrayPairs sz f b keys values
      ContentsNodes nodes -> foldrArray (sz + 1) go b nodes

foldrPrimArrayPairs :: forall m k v b. (PrimMonad m, Ord k, Prim k, Prim v)
  => Int -- ^ length of arrays
  -> (k -> v -> b -> m b)
  -> b
  -> MutablePrimArray (PrimState m) k
  -> MutablePrimArray (PrimState m) v
  -> m b
foldrPrimArrayPairs len f b0 ks vs = go (len - 1) b0
  where
  go :: Int -> b -> m b
  go !ix !b1 = if ix >= 0
    then do
      k <- readPrimArray ks ix
      v <- readPrimArray vs ix
      b2 <- f k v b1
      go (ix - 1) b2
    else return b1

foldrArray :: forall m a b (c :: Heap). (PrimMonad m, Contractible a)
  => Int -- ^ length of array
  -> (a (PrimState m) c -> b -> m b)
  -> b
  -> ContractedMutableArray a (PrimState m) c
  -> m b
foldrArray len f b0 arr = go (len - 1) b0
  where
  go :: Int -> b -> m b
  go !ix !b1 = if ix >= 0
    then do
      a <- readContractedArray arr ix
      b2 <- f a b1
      go (ix - 1) b2
    else return b1

-- | This lookup is O(log n). It provides the index of the
--   first element greater than the argument.
--   Precondition, the array provided is sorted low to high.
{-# INLINABLE findIndexOfGtElem #-}
findIndexOfGtElem :: forall m a. (Ord a, Prim a, PrimMonad m) => MutablePrimArray (PrimState m) a -> a -> Int -> m Int
findIndexOfGtElem v needle sz = go 0 (sz - 1)
  where
  go :: Int -> Int -> m Int
  go !lo !hi = if lo <= hi
    then do
      let !mid = lo + half (hi - lo)
      !val <- readPrimArray v mid
      if | val == needle -> return (mid + 1)
         | val < needle -> go (mid + 1) hi
         | otherwise -> go lo (mid - 1)
    else return lo

-- -- | This lookup is O(log n). It provides the index of the
-- --   match, or it returns (-1) to indicate that there was
-- --   no match.
-- {-# INLINABLE lookupSorted #-}
-- lookupSorted :: forall m a. (Ord a, Prim a, PrimMonad m) => MutablePrimArray (PrimState m) a -> a -> m Int
-- lookupSorted v needle = do
--   sz <- getSizeofMutablePrimArray v
--   go (-1) 0 (sz - 1)
--   where
--   go :: Int -> Int -> Int -> m Int
--   go !result !lo !hi = if lo <= hi
--     then do
--       let !mid = lo + half (hi - lo)
--       !val <- readPrimArray v mid
--       if | val == needle -> go mid lo (mid - 1)
--          | val < needle -> go result (mid + 1) hi
--          | otherwise -> go result lo (mid - 1)
--     else return result

{-# INLINE half #-}
half :: Int -> Int
half x = unsafeShiftR x 1
