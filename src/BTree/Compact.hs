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
  , Context
  , new
  , newContext
  , debugMap
  , insert
  , modifyWithM
  , lookup
  , toAscList
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

-- One easy improvement I would like to make is to change
-- the way that sizing is being handled. Now that all of
-- the BTrees get serialized to bytearrays (and arrayarrays),
-- we should just be able to stick the size directly
-- into the BTree without doing the weird indirection trick.
-- The only tricky thing is that we will have to update the
-- size of a node on our way back up after an insertion.
-- This will required modifying the Insert data type.

data Context s c = Context
  { _contextDegree :: {-# UNPACK #-} !Int
  , _contextToken :: {-# UNPACK #-} !(Token c)
  , _contextSizing :: {-# UNPACK #-} !(MutVar s (Sizing s c))
  }

-- Use mkBTree instead. Using this for pattern matching is ok. 
data BTree k v s (c :: Heap)
  = BTree
    {-# UNPACK #-} !(Sizing s c) -- block and index for current size
    {-# UNPACK #-} !(MutablePrimArray s k)
    {-# UNPACK #-} !(FlattenedContents k v s c)

-- In defining this instance, we make the assumption that an
-- Addr and an Int have the same size.
instance Contractible (BTree k v) where
  unsafeContractedUnliftedPtrCount# _ = 5#
  unsafeContractedByteCount# _ = sizeOf# (undefined :: Int) *# 2#
  readContractedArray# ba aa ix s1 =
    let ixByte = ix *# 2#
        ixPtr = ix *# 5#
     in case readIntArray# ba (ixByte +# 0#) s1 of
         (# s2, szIx #) -> case readIntArray# ba (ixByte +# 1#) s2 of
          (# s3, toggle #) -> case readMutableByteArrayArray# aa (ixPtr +# 0#) s3 of
           (# s4, szBlock #) -> case readMutableByteArrayArray# aa (ixPtr +# 1#) s4 of
            (# s5, keys #) -> case readMutableByteArrayArray# aa (ixPtr +# 2#) s5 of
             (# s6, values #) -> case readMutableByteArrayArray# aa (ixPtr +# 3#) s6 of
              (# s7, nodesBytes #) -> case readMutableArrayArrayArray# aa (ixPtr +# 4#) s7 of
               (# s8, nodesPtrs #) ->
                (# s8, (BTree (Sizing (I# szIx) (MutablePrimArray szBlock)) (MutablePrimArray keys) (FlattenedContents (I# toggle) (MutablePrimArray values) (ContractedMutableArray nodesBytes nodesPtrs))) #)
         
  writeContractedArray# ba aa ix (BTree (Sizing (I# szIx) (MutablePrimArray szBlock)) (MutablePrimArray keys) (FlattenedContents (I# toggle) (MutablePrimArray values) (ContractedMutableArray nodesBytes nodesPtrs))) s1 =
    let ixByte = ix *# 2#
        ixPtr = ix *# 5#
     in case writeIntArray# ba (ixByte +# 0#) szIx s1 of
         s2 -> case writeIntArray# ba (ixByte +# 1#) toggle s2 of
          s3 -> case writeMutableByteArrayArray# aa (ixPtr +# 0#) szBlock s3 of
           s4 -> case writeMutableByteArrayArray# aa (ixPtr +# 1#) keys s4 of
            s5 -> case writeMutableByteArrayArray# aa (ixPtr +# 2#) values s5 of
             s6 -> case writeMutableByteArrayArray# aa (ixPtr +# 3#) nodesBytes s6 of
              s7 -> writeMutableArrayArrayArray# aa (ixPtr +# 4#) nodesPtrs s7
   

data Sizing s (c :: Heap) = Sizing
  {-# UNPACK #-} !Int
  -- The array index does not live in the compact region
  {-# UNPACK #-} !(MutablePrimArray s Word16)
  -- This array must live in the compact region that the
  -- token in the Context refers to.

packedSizesCount :: Int
packedSizesCount = 2040

newContext :: (PrimMonad m) => Int -> Token c -> m (Context (PrimState m) c)
newContext deg token = do
  !sizes0 <- compactAddGeneral token =<< newPrimArray packedSizesCount
  let !sizing0 = Sizing 0 sizes0
  ref <- newMutVar sizing0
  return (Context deg token ref) -- newCompactArray' newKeyArray newValueArray)


-- We manually flatten this sum type so that it can be unpacked
-- into BTree.
data FlattenedContents k v s c = FlattenedContents
  {-# UNPACK #-} !Int
  {-# UNPACK #-} !(MutablePrimArray s v)
  {-# UNPACK #-} !(ContractedMutableArray (BTree k v) s c)

data Contents k v s c
  = ContentsValues {-# UNPACK #-} !(MutablePrimArray s v)
  | ContentsNodes {-# UNPACK #-} !(ContractedMutableArray (BTree k v) s c)

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
  -> ContractedMutableArray (BTree k v) s c -- ^ garbage value
  -> Contents k v s c
  -> FlattenedContents k v s c
contentsToFlattenContents !garbageValues !garbageNodes !c = case c of
  ContentsValues values -> FlattenedContents 0 values garbageNodes
  ContentsNodes nodes -> FlattenedContents 1 garbageValues nodes 

-- | Get the nodes out, even if they are garbage. This is used
--   to get a garbage value when needed.
{-# INLINE demandFlattenedContentsNodes #-}
demandFlattenedContentsNodes :: FlattenedContents k v s c -> ContractedMutableArray (BTree k v) s c
demandFlattenedContentsNodes (FlattenedContents _ _ nodes) = nodes

data Insert k v s c
  = Ok !v
  | Split
      {-# NOUNPACK #-} !(BTree k v s c)
      !k
      !v
      {-# UNPACK #-} !(Sizing s c)
      -- ^ The new node that will go to the right,
      --   the key propagated to the parent,
      --   the inserted value, updated sizing info.

{-# INLINE mkBTree #-}
mkBTree :: PrimMonad m
  => Token c
  -> ContractedMutableArray (BTree k v) (PrimState m) c -- ^ garbage value
  -> Sizing (PrimState m) c
  -> MutablePrimArray (PrimState m) k -- ^ keys
  -> Contents k v (PrimState m) c
  -> m (BTree k v (PrimState m) c)
mkBTree token garbage a b c = do
  let !garbageValues = coercePrimArray b
      !bt = BTree a b (contentsToFlattenContents garbageValues garbage c)
  compactAddGeneral token bt

coercePrimArray :: MutablePrimArray s a -> MutablePrimArray s b
coercePrimArray (MutablePrimArray a) = MutablePrimArray a

new :: (PrimMonad m, Prim k, Prim v)
  => Context (PrimState m) c
  -> m (BTree k v (PrimState m) c)
new (Context !degree !token !szRef) = do
  if degree < 3
    then error "Btree.new: max nodes per child cannot be less than 3"
    else return ()
  !sizing0 <- readMutVar szRef
  writeNodeSize sizing0 0
  writeMutVar szRef =<< nextSizing token sizing0
  !keys <- newPrimArray (degree - 1)
  !values <- newPrimArray (degree - 1)
  -- it kind of pains me that this is needed, but since
  -- we only do it once when calling @new@, it should
  -- not hurt performance at all.
  !garbageNodes <- newContractedArray token 0
  mkBTree token garbageNodes sizing0 keys (ContentsValues values)

-- {-# SPECIALIZE lookup :: BTree RealWorld Int Int c -> Int -> IO (Maybe Int) #-}
{-# INLINABLE lookup #-}
lookup :: forall m k v c. (PrimMonad m, Ord k, Prim k, Prim v)
  => BTree k v (PrimState m) c -> k -> m (Maybe v)
lookup theNode k = go 0 theNode
  where
  go :: Int -> BTree k v (PrimState m) c -> m (Maybe v)
  go !n (BTree sizing@(Sizing _szIx _) keys c@(FlattenedContents _tog _ _)) = do
    sz <- readNodeSize sizing
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
        go (n + 1) node

_addrToPtr :: Addr -> Ptr Word8
_addrToPtr (Addr a) = Ptr a


{-# INLINE insert #-}
insert :: (Ord k, Prim k, Prim v, PrimMonad m)
  => Context (PrimState m) c
  -> BTree k v (PrimState m) c
  -> k
  -> v
  -> m (BTree k v (PrimState m) c)
insert !ctx !m !k !v = do
  !(!_,!node) <- modifyWithM ctx m k v (\_ -> return (Replace v))
  return node

data Decision a = Keep | Replace !a

-- When we turn on this specialize pragma, it gets way faster
-- for the particular case.
{-# SPECIALIZE modifyWithM :: Context RealWorld c -> BTree Int Int RealWorld c -> Int -> Int -> (Int -> IO (Decision Int)) -> IO (Int, BTree Int Int RealWorld c) #-}
{-# INLINABLE modifyWithM #-}
modifyWithM :: forall m k v c. (Ord k, Prim k, Prim v, PrimMonad m)
  => Context (PrimState m) c
  -> BTree k v (PrimState m) c
  -> k
  -> v -- ^ value to insert if key not found
  -> (v -> m (Decision v)) -- ^ modification to value if key is found
  -> m (v, BTree k v (PrimState m) c)
modifyWithM (Context !degree !token !sizingRef) !root !k !newValue alter = do
  -- I believe I have been enlightened.
  !ins <- go root
  case ins of
    Ok v -> return (v,root)
    Split !rightNode newRootKey v sizing -> do
      writeNodeSize sizing 1
      newRootKeys <- newPrimArray (degree - 1)
      writePrimArray newRootKeys 0 newRootKey
      !newRootChildren <- newContractedArray token degree
      let !leftNode = root
      !newRoot@(BTree _ _ (FlattenedContents _ _ cmptRootChildren)) <- mkBTree token newRootChildren sizing newRootKeys (ContentsNodes newRootChildren)
      writeContractedArray cmptRootChildren 0 leftNode
      writeContractedArray cmptRootChildren 1 rightNode
      !newSizing <- nextSizing token sizing
      writeMutVar sizingRef newSizing
      return (v,newRoot)
  where
  go :: BTree k v (PrimState m) c -> m (Insert k v (PrimState m) c)
  go (BTree !szRef !keys !c) = do
    !sz <- readNodeSize szRef
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
                writeNodeSize szRef (sz + 1)
                unsafeInsertPrimArray sz gtIx k keys
                unsafeInsertPrimArray sz gtIx v values
                return (Ok v)
              else do
                -- We do not have enough space. The node must be split.
                let !leftSize = div sz 2
                    !rightSize = sz - leftSize
                    !leftKeys = keys
                    !leftValues = values
                rightSzRef <- readMutVar sizingRef
                rightKeys <- newPrimArray (degree - 1)
                rightValues <- newPrimArray (degree - 1)
                if gtIx < leftSize
                  then do
                    writeNodeSize rightSzRef rightSize
                    copyMutablePrimArray rightKeys 0 leftKeys leftSize rightSize
                    copyMutablePrimArray rightValues 0 leftValues leftSize rightSize
                    unsafeInsertPrimArray leftSize gtIx k leftKeys
                    unsafeInsertPrimArray leftSize gtIx v leftValues
                    writeNodeSize szRef (leftSize + 1)
                  else do
                    writeNodeSize rightSzRef (rightSize + 1)
                    -- Currently, we're copying from left to right and
                    -- then doing another copy from right to right. We
                    -- might be able to do better. We could do the same number
                    -- of memcpys but copy fewer total elements and not
                    -- have the slowdown caused by overlap.
                    copyMutablePrimArray rightKeys 0 leftKeys leftSize rightSize
                    copyMutablePrimArray rightValues 0 leftValues leftSize rightSize
                    unsafeInsertPrimArray rightSize (gtIx - leftSize) k rightKeys
                    unsafeInsertPrimArray rightSize (gtIx - leftSize) v rightValues
                    writeNodeSize szRef leftSize
                !propagated <- readPrimArray rightKeys 0
                !newSizing <- nextSizing token rightSzRef
                !newTree <- mkBTree token (demandFlattenedContentsNodes c) rightSzRef rightKeys (ContentsValues rightValues)
                return (Split newTree propagated v newSizing)
          else do
            !v <- readPrimArray values ix
            !dec <- alter v
            !v' <- case dec of
              Keep -> return v
              Replace v' -> writePrimArray values ix v' >> return v'
            return (Ok v')
      ContentsNodes nodes -> do
        !(!gtIx,!isEq) <- findIndexGte keys k sz
        -- case e of
        --   Right _ -> error "write Right case"
        --   Left gtIx -> do
        !node <- readContractedArray nodes (if isEq then gtIx + 1 else gtIx)
        !ins <- go node
        case ins of
          Ok !v -> return (Ok v)
          Split !rightNode !propagated !v !sizing -> if sz < degree - 1
            then do
              unsafeInsertPrimArray sz gtIx propagated keys
              unsafeInsertContractedArray (sz + 1) (gtIx + 1) rightNode nodes
              writeNodeSize szRef (sz + 1)
              writeMutVar sizingRef sizing
              return (Ok v)
            else do
              let !middleIx = div sz 2
                  !leftKeys = keys
                  !leftNodes = nodes
                  !rightSzRef = sizing
              !middleKey <- readPrimArray keys middleIx
              !rightKeysOnHeap <- newPrimArray (degree - 1)
              !rightNodes' <- newContractedArray token degree -- uninitializedNode
              !x@(BTree _ rightKeys (FlattenedContents _ _ rightNodes)) <- mkBTree token rightNodes' rightSzRef rightKeysOnHeap (ContentsNodes rightNodes')
              let !leftSize = middleIx
                  !rightSize = sz - leftSize
              if middleIx >= gtIx
                then do
                  copyMutablePrimArray rightKeys 0 leftKeys (leftSize + 1) (rightSize - 1)
                  copyContractedMutableArray rightNodes 0 leftNodes (leftSize + 1) rightSize
                  unsafeInsertPrimArray leftSize gtIx propagated leftKeys
                  unsafeInsertContractedArray (leftSize + 1) (gtIx + 1) rightNode leftNodes
                  writeNodeSize szRef (leftSize + 1)
                  writeNodeSize rightSzRef (rightSize - 1)
                else do
                  -- Currently, we're copying from left to right and
                  -- then doing another copy from right to right. We can do better.
                  -- There is a similar note further up.
                  copyMutablePrimArray rightKeys 0 leftKeys (leftSize + 1) (rightSize - 1)
                  copyContractedMutableArray rightNodes 0 leftNodes (leftSize + 1) rightSize
                  unsafeInsertPrimArray (rightSize - 1) (gtIx - leftSize - 1) propagated rightKeys
                  unsafeInsertContractedArray rightSize (gtIx - leftSize) rightNode rightNodes
                  writeNodeSize szRef leftSize
                  writeNodeSize rightSzRef rightSize
              !newSizing <- nextSizing token rightSzRef
              return (Split x middleKey v newSizing)

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
  => Context (PrimState m) c
  -> BTree k v (PrimState m) c
  -> m String
-- debugMap (Context _ _ _ _ _) BTreeUnused = return "BTreeUnused, should not happen"
debugMap (Context _ _ _) (BTree !rootSizing !rootKeys !rootContents) = do
  !rootSz <- readNodeSize rootSizing
  let go :: Int -> Int -> MutablePrimArray (PrimState m) k -> FlattenedContents k v (PrimState m) c -> m [(Int,String)]
      go level sz keys c = case flattenContentsToContents c of
        ContentsValues values -> do
          pairStrs <- showPairs sz keys values
          return (map (\s -> (level,s)) pairStrs)
        ContentsNodes nodes -> do
          pairs <- pairForM sz keys nodes
            $ \k (BTree theNextSizing nextKeys nextContents) -> do
              nextSz <- readNodeSize theNextSizing
              nextStrs <- go (level + 1) nextSz nextKeys nextContents
              return (nextStrs ++ [(level,show k)]) -- ++ " (Size: " ++ show nextSz ++ ")")])
          -- I think this should always end up being in bounds
          BTree lastSizing lastKeys lastContents <- readContractedArray nodes sz
          lastSz <- readNodeSize lastSizing
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
  => Context (PrimState m) c
  -> BTree k v (PrimState m) c
  -> m [(k,v)]
toAscList = foldrWithKey f []
  where
  f :: k -> v -> [(k,v)] -> m [(k,v)]
  f k v xs = return ((k,v) : xs)

readNodeSize :: PrimMonad m => Sizing (PrimState m) c -> m Int
readNodeSize (Sizing ix m) = do
  w16 <- readPrimArray m ix
  return (fromIntegral w16)

nextSizing :: PrimMonad m => Token c -> Sizing (PrimState m) c -> m (Sizing (PrimState m) c)
nextSizing !token (Sizing !ix !marr) =
  if ix < packedSizesCount - 1
    then return (Sizing (ix + 1) marr)
    else do
      marr' <- compactAddGeneral token =<< newPrimArray packedSizesCount
      return (Sizing 0 marr')

writeNodeSize :: PrimMonad m => Sizing (PrimState m) c -> Int -> m ()
writeNodeSize (Sizing ix m) sz = writePrimArray m ix (fromIntegral sz)

foldrWithKey :: forall m k v b c. (PrimMonad m, Ord k, Prim k, Prim v)
  => (k -> v -> b -> m b)
  -> b
  -> Context (PrimState m) c
  -> BTree k v (PrimState m) c
  -> m b
foldrWithKey f b0 (Context _ _ _) root = flip go b0 root
  where
  go :: BTree k v (PrimState m) c -> b -> m b
  -- go BTreeUnused !b = return b -- should not happen
  go (BTree sizing keys c) !b = do
    sz <- readNodeSize sizing
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
