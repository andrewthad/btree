{-# LANGUAGE LambdaCase #-}
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

module BTree.ContractibleForall
  ( BTree
  , Decision(..)
  , new
  , modifyWithM
  , lookup
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

data BTree k (v :: * -> Heap -> *) s (c :: Heap) = BTree
  {-# UNPACK #-} !Int -- degree
  {-# UNPACK #-} !(BNode k v s c)

-- Use mkBTree instead. Using this for pattern matching is ok. 
data BNode k (v :: * -> Heap -> *) s (c :: Heap) = BNode
  { _bnodeSize :: {-# UNPACK #-} !Int -- size, number of keys present in node
  , _bnodeKeys :: {-# UNPACK #-} !(MutablePrimArray s k)
  , _bnodeContents :: {-# UNPACK #-} !(FlattenedContents k v s c)
  }

-- In defining this instance, we make the assumption that an
-- Addr and an Int have the same size.
instance Contractible (BNode k v) where
  unsafeContractedUnliftedPtrCount# _ = 5#
  unsafeContractedByteCount# _ = sizeOf# (undefined :: Int) *# 2#
  readContractedArray# ba aa ix s1 =
    let ixByte = ix *# 2#
        ixPtr = ix *# 5#
     in case readIntArray# ba (ixByte +# 0#) s1 of
         (# s2, sz #) -> case readIntArray# ba (ixByte +# 1#) s2 of
          (# s3, toggle #) -> case readMutableByteArrayArray# aa (ixPtr +# 0#) s3 of
           (# s4, keys #) -> case readMutableByteArrayArray# aa (ixPtr +# 1#) s4 of
            (# s5, valuesBytes #) -> case readMutableByteArrayArray# aa (ixPtr +# 2#) s5 of
             (# s6, nodesBytes #) -> case readMutableArrayArrayArray# aa (ixPtr +# 3#) s6 of
              (# s7, nodesPtrs #) -> case readMutableArrayArrayArray# aa (ixPtr +# 4#) s7 of
               (# s8, valuesPtrs #) ->
                (# s8, (BNode (I# sz) (MutablePrimArray keys) (FlattenedContents (I# toggle) (ContractedMutableArray valuesBytes valuesPtrs) (ContractedMutableArray nodesBytes nodesPtrs))) #)
  writeContractedArray# ba aa ix (BNode (I# sz) (MutablePrimArray keys) (FlattenedContents (I# toggle) (ContractedMutableArray valuesBytes valuesPtrs) (ContractedMutableArray nodesBytes nodesPtrs))) s1 =
    let ixByte = ix *# 2#
        ixPtr = ix *# 5#
     in case writeIntArray# ba (ixByte +# 0#) sz s1 of
         s2 -> case writeIntArray# ba (ixByte +# 1#) toggle s2 of
          s3 -> case writeMutableByteArrayArray# aa (ixPtr +# 0#) keys s3 of
           s4 -> case writeMutableByteArrayArray# aa (ixPtr +# 1#) valuesBytes s4 of
            s5 -> case writeMutableByteArrayArray# aa (ixPtr +# 2#) nodesBytes s5 of
             s6 -> case writeMutableArrayArrayArray# aa (ixPtr +# 3#) nodesPtrs s6 of
              s7 -> writeMutableArrayArrayArray# aa (ixPtr +# 4#) valuesPtrs s7

instance Contractible (BTree k v) where
  unsafeContractedUnliftedPtrCount# _ = 5#
  unsafeContractedByteCount# _ = sizeOf# (undefined :: Int) *# 3#
  readContractedArray# ba aa ix s1 =
    let ixByte = ix *# 3#
        ixPtr = ix *# 5#
     in case readIntArray# ba (ixByte +# 0#) s1 of
         (# s2, sz #) -> case readIntArray# ba (ixByte +# 1#) s2 of
          (# s3, toggle #) -> case readIntArray# ba (ixByte +# 2#) s3 of
           (# s4, degree #) -> case readMutableByteArrayArray# aa (ixPtr +# 0#) s4 of
            (# s5, keys #) -> case readMutableByteArrayArray# aa (ixPtr +# 1#) s5 of
             (# s6, valuesBytes #) -> case readMutableByteArrayArray# aa (ixPtr +# 2#) s6 of
              (# s7, nodesBytes #) -> case readMutableArrayArrayArray# aa (ixPtr +# 3#) s7 of
               (# s8, nodesPtrs #) -> case readMutableArrayArrayArray# aa (ixPtr +# 4#) s8 of
                (# s9, valuesPtrs #) ->
                 (# s9, BTree (I# degree) (BNode (I# sz) (MutablePrimArray keys) (FlattenedContents (I# toggle) (ContractedMutableArray valuesBytes valuesPtrs) (ContractedMutableArray nodesBytes nodesPtrs))) #)
  writeContractedArray# ba aa ix (BTree (I# degree) (BNode (I# sz) (MutablePrimArray keys) (FlattenedContents (I# toggle) (ContractedMutableArray valuesBytes valuesPtrs) (ContractedMutableArray nodesBytes nodesPtrs)))) s1 =
    let ixByte = ix *# 3#
        ixPtr = ix *# 5#
     in case writeIntArray# ba (ixByte +# 0#) sz s1 of
         s2 -> case writeIntArray# ba (ixByte +# 1#) toggle s2 of
          s3 -> case writeIntArray# ba (ixByte +# 2#) degree s3 of
           s4 -> case writeMutableByteArrayArray# aa (ixPtr +# 0#) keys s4 of
            s5 -> case writeMutableByteArrayArray# aa (ixPtr +# 1#) valuesBytes s5 of
             s6 -> case writeMutableByteArrayArray# aa (ixPtr +# 2#) nodesBytes s6 of
              s7 -> case writeMutableArrayArrayArray# aa (ixPtr +# 3#) nodesPtrs s7 of
               s8 -> writeMutableArrayArrayArray# aa (ixPtr +# 4#) valuesPtrs s8
   
-- We manually flatten this sum type so that it can be unpacked
-- into BNode.
data FlattenedContents (k :: *) (v :: * -> Heap -> *) (s :: *) (c :: Heap) = FlattenedContents
  {-# UNPACK #-} !Int
  {-# UNPACK #-} !(ContractedMutableArray v s c)
  {-# UNPACK #-} !(ContractedMutableArray (BNode k v) s c)

data Contents (k :: *) (v :: * -> Heap -> *) (s :: *) (c :: Heap)
  = ContentsValues {-# UNPACK #-} !(ContractedMutableArray v s c)
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
     ContractedMutableArray v s c -- ^ garbage value
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

data Insert k v s c r
  = Ok
      !r
      {-# UNPACK #-} !Int -- new size of left child
  | Split
      {-# NOUNPACK #-} !(BNode k v s c)
      !k
      !r
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
  let !garbageValues = coerceContactedArray garbage
      !bt = BNode a b (contentsToFlattenContents garbageValues garbage c)
  compactAddGeneral token bt

coerceContactedArray :: ContractedMutableArray a s c -> ContractedMutableArray b s c
coerceContactedArray (ContractedMutableArray a b) = ContractedMutableArray a b

new :: (PrimMonad m, Prim k, ContractibleForall v)
  => Token c
  -> Int -- ^ degree, must be at least 3
  -> ContractibleForallWitness v
  -> m (BTree k v (PrimState m) c)
new !token !degree !w = do
  if degree < 3
    then error "Btree.new: max nodes per child cannot be less than 3"
    else return ()
  !keys <- newPrimArray (degree - 1)
  !values <- newContractedForallArray token (degree - 1) w
  -- it kind of pains me that this is needed, but since
  -- we only do it once when calling @new@, it should
  -- not hurt performance at all.
  !garbageNodes <- newContractedArray token 0
  node <- mkBTree token garbageNodes 0 keys (ContentsValues values)
  return (BTree degree node)

-- {-# SPECIALIZE lookup :: BNode RealWorld Int Int c -> Int -> IO (Maybe Int) #-}
{-# INLINABLE lookup #-}
lookup :: forall m k v c. (PrimMonad m, Ord k, Prim k, ContractibleForall v)
  => BTree k v (PrimState m) c -> k -> ContractibleForallWitness v -> m (Maybe (v (PrimState m) c))
lookup (BTree _ theNode) k w = go theNode
  where
  go :: BNode k v (PrimState m) c -> m (Maybe (v (PrimState m) c))
  go (BNode sz keys c@(FlattenedContents _tog _ _)) = do
    case flattenContentsToContents c of
      ContentsValues values -> do
        ix <- findIndex keys k sz
        if ix < 0
          then return Nothing
          else do
            v <- readContractedForallArray values ix w
            return (Just v)
      ContentsNodes nodes -> do
        ix <- findIndexOfGtElem keys k sz
        !node <- readContractedArray nodes ix
        go node

data Decision r a = Keep !r | Replace !r !a

-- When we turn on this specialize pragma, it gets way faster
-- for the particular case.
-- {-# SPECIALIZE modifyWithM :: Token c -> BTree Int Int RealWorld c -> Int -> Int -> (Int -> IO (Decision Int)) -> IO (Int, BTree Int Int RealWorld c) #-}
{-# INLINABLE modifyWithM #-}
modifyWithM :: forall m k v c r. (Ord k, Prim k, ContractibleForall v, PrimMonad m)
  => Token c
  -> BTree k v (PrimState m) c
  -> k
  -> m (v (PrimState m) c) -- ^ value to insert if key not found
  -> (v (PrimState m) c -> m (Decision r (v (PrimState m) c))) -- ^ modification to value if key is found
  -> ContractibleForallWitness v
  -> m (r, BTree k v (PrimState m) c)
modifyWithM !token (BTree !degree !root) !k !newValue alter !w = do
  !ins <- go root
  case ins of
    Ok !r !newNodeSz -> return (r,BTree degree (root { _bnodeSize = newNodeSz }))
    Split !rightNode !newRootKey !r !newLeftSize -> do
      newRootKeys <- newPrimArray (degree - 1)
      writePrimArray newRootKeys 0 newRootKey
      !newRootChildren <- newContractedArray token degree
      let !leftNode = root { _bnodeSize = newLeftSize }
      !newRoot@(BNode _ _ (FlattenedContents _ _ cmptRootChildren)) <- mkBTree token newRootChildren 1 newRootKeys (ContentsNodes newRootChildren)
      writeContractedArray cmptRootChildren 0 leftNode
      writeContractedArray cmptRootChildren 1 rightNode
      return (r,BTree degree newRoot)
  where
  go :: BNode k v (PrimState m) c -> m (Insert k v (PrimState m) c r)
  go (BNode !sz !keys !c) = do
    case flattenContentsToContents c of
      ContentsValues !values -> do
        !ix <- findIndex keys k sz
        if ix < 0
          then do
            let !gtIx = decodeGtIndex ix
            (v,r) <- newValue >>= \v0 -> alter v0 >>= \case
              Keep r -> return (v0,r)
              Replace r v1 -> return (v1,r)
            if sz < degree - 1
              then do
                -- We have enough space
                unsafeInsertPrimArray sz gtIx k keys
                unsafeInsertContractedForallArray sz gtIx v values w
                return (Ok r (sz + 1))
              else do
                -- We do not have enough space. The node must be split.
                let !leftSize = div sz 2
                    !rightSize = sz - leftSize
                    !leftKeys = keys
                    !leftValues = values
                rightKeys' <- newPrimArray (degree - 1)
                rightValues' <- newContractedForallArray token (degree - 1) w
                let (newLeftSz,actualRightSz) = if gtIx < leftSize
                      then (leftSize + 1, rightSize)
                      else (leftSize,rightSize + 1)
                !newTree@(BNode _ rightKeys (FlattenedContents _ rightValues _)) <- mkBTree token (demandFlattenedContentsNodes c) actualRightSz rightKeys' (ContentsValues rightValues')
                if gtIx < leftSize
                  then do
                    copyMutablePrimArray rightKeys 0 leftKeys leftSize rightSize
                    copyContractedForallMutableArray rightValues 0 leftValues leftSize rightSize w
                    unsafeInsertPrimArray leftSize gtIx k leftKeys
                    unsafeInsertContractedForallArray leftSize gtIx v leftValues w
                  else do
                    -- Currently, we're copying from left to right and
                    -- then doing another copy from right to right. We
                    -- might be able to do better. We could do the same number
                    -- of memcpys but copy fewer total elements and not
                    -- have the slowdown caused by overlap.
                    copyMutablePrimArray rightKeys 0 leftKeys leftSize rightSize
                    copyContractedForallMutableArray rightValues 0 leftValues leftSize rightSize w
                    unsafeInsertPrimArray rightSize (gtIx - leftSize) k rightKeys
                    unsafeInsertContractedForallArray rightSize (gtIx - leftSize) v rightValues w
                !propagated <- readPrimArray rightKeys 0
                return (Split newTree propagated r newLeftSz)
          else do
            !v <- readContractedForallArray values ix w
            !dec <- alter v
            !r <- case dec of
              Keep r -> return r
              Replace r v' -> writeContractedForallArray values ix v' >> return r
            return (Ok r sz)
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

foldrWithKey :: forall m k v b c. (PrimMonad m, Ord k, Prim k, ContractibleForall v)
  => (k -> v (PrimState m) c -> b -> m b)
  -> b
  -> BTree k v (PrimState m) c
  -> ContractibleForallWitness v
  -> m b
foldrWithKey f b0 (BTree _ root) w = flip go b0 root
  where
  go :: BNode k v (PrimState m) c -> b -> m b
  go (BNode sz keys c) !b = do
    case flattenContentsToContents c of
      ContentsValues values -> foldrPrimArrayPairs sz f b keys values w
      ContentsNodes nodes -> foldrArray (sz + 1) go b nodes

foldrPrimArrayPairs :: forall m k v b c. (PrimMonad m, Ord k, Prim k, ContractibleForall v)
  => Int -- ^ length of arrays
  -> (k -> v (PrimState m) c -> b -> m b)
  -> b
  -> MutablePrimArray (PrimState m) k
  -> ContractedMutableArray v (PrimState m) c
  -> ContractibleForallWitness v
  -> m b
foldrPrimArrayPairs len f b0 ks vs !w = go (len - 1) b0
  where
  go :: Int -> b -> m b
  go !ix !b1 = if ix >= 0
    then do
      k <- readPrimArray ks ix
      v <- readContractedForallArray vs ix w
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
