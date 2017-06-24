{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE Strict #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE UnboxedSums #-}
{-# LANGUAGE MagicHash #-}

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

import Data.Primitive.PrimRef
import Data.Primitive.PrimArray
import Data.Primitive.MutVar

data Context s c = Context
  { _contextDegree :: {-# UNPACK #-} !Int
  , _contextToken :: {-# UNPACK #-} !(Token c)
  , _contextSizing :: {-# UNPACK #-} !(MutVar s (Sizing s c))
  -- , _contextSizeIndex :: {-# UNPACK #-} !(PrimRef s Int)
  --   -- ^ The array index does not live in the compact region
  -- , _contextSizeBuffer :: {-# UNPACK #-} !(MutVar s (MutablePrimArray s Word16))
  --   -- ^ This MutVar does not live in the compact region,
  --   --   but the array inside it must live in the compact region.
  }

data Sizing s c = Sizing
  {-# UNPACK #-} !Int
  -- The array index does not live in the compact region
  {-# UNPACK #-} !(MutablePrimArray s Word16)
  -- This array must live in the compact region that the
  -- token in the Context refers to.

packedSizesCount :: Int
packedSizesCount = 2040

newContext :: (PrimMonad m) => Int -> Token c -> m (Context (PrimState m) c)
newContext deg token = do
  -- newCompactArray' <- newCompactArrayCopier token deg
  -- newKeyArray <- newCompactPrimArrayCopier token (deg - 1)
  -- newValueArray <- newCompactPrimArrayCopier token (deg - 1)
  !sizes0 <- compactAddGeneral token =<< newPrimArray packedSizesCount
  let !sizing0 = Sizing 0 sizes0
  ref <- newMutVar sizing0
  return (Context deg token ref) -- newCompactArray' newKeyArray newValueArray)

-- Using this data constructor to construct is unsafe. For that
-- purpose, use mkBTree instead. Using this for pattern matching is ok. 
data BTree s k v c
  = BTree
    {-# UNPACK #-} !(Sizing s c) -- block and index for current size
    {-# UNPACK #-} !(MutablePrimArray s k)
    !(Contents s k v c)
  -- | BTreeUnused -- this is to prevent unpacking into functions

data Contents s k v c
  = ContentsValues {-# UNPACK #-} !(MutablePrimArray s v)
  | ContentsNodes {-# UNPACK #-} !(CompactMutableArray s (BTree s k v) c)

data Insert s k v c
  = Ok !v
  | Split
      {-# NOUNPACK #-} !(BTree s k v c)
      !k
      !v
      {-# UNPACK #-} !(Sizing s c)
      -- ^ The new node that will go to the right,
      --   the key propagated to the parent,
      --   the inserted value, updated sizing info.

mkBTree :: PrimMonad m
  => Token c
  -> Sizing (PrimState m) c
  -> MutablePrimArray (PrimState m) k
  -> Contents (PrimState m) k v c
  -> m (BTree (PrimState m) k v c)
mkBTree token a b c = do
  let !bt = BTree a b c
  compactAddGeneral token bt

new :: (PrimMonad m, Prim k, Prim v)
  => Context (PrimState m) c
  -> m (BTree (PrimState m) k v c)
new (Context !degree !token !szRef) = do
  if degree < 3
    then error "Btree.new: max nodes per child cannot be less than 3"
    else return ()
  !sizing0 <- readMutVar szRef
  writeNodeSize sizing0 0
  writeMutVar szRef =<< nextSizing token sizing0
  !keys <- newPrimArray (degree - 1)
  !values <- newPrimArray (degree - 1)
  mkBTree token sizing0 keys (ContentsValues values)

lookup :: forall m k v c. (PrimMonad m, Ord k, Prim k, Prim v)
  => BTree (PrimState m) k v c -> k -> m (Maybe v)
lookup theNode k = go theNode
  where
  go :: BTree (PrimState m) k v c -> m (Maybe v)
  go (BTree sizing keys c) = do
    sz <- readNodeSize sizing
    case c of
      ContentsValues values -> do
        e <- findIndex keys k sz
        case e of
          Left _ -> return Nothing
          Right ix -> do
            v <- readPrimArray values ix
            return (Just v)
      ContentsNodes nodes -> do
        ix <- findIndexBetween keys k sz
        go =<< readCompactArray nodes ix

{-# INLINE insert #-}
insert :: (Ord k, Prim k, Prim v, PrimMonad m)
  => Context (PrimState m) c
  -> BTree (PrimState m) k v c
  -> k
  -> v
  -> m (BTree (PrimState m) k v c)
insert !ctx !m !k !v = do
  !(!_,!node) <- modifyWithM ctx m k (\_ -> return v)
  return node

-- {-# SPECIALIZE modifyWithM :: (Ord k, Prim k, Prim v) => Context s c -> BTree s k v c -> k -> (Maybe v -> ST s v) -> ST s (v, BTree s k v c) #-}
-- {-# SPECIALIZE modifyWithM :: (Ord k, Prim k, Prim v) => Context RealWorld c -> BTree RealWorld k v c -> k -> (Maybe v -> IO v) -> IO (v, BTree RealWorld k v c) #-}
--
-- When we turn on this specialize pragma, it gets way faster
-- for the particular case.
-- {-# SPECIALIZE modifyWithM :: Context RealWorld c -> BTree RealWorld Int Int c -> Int -> (Maybe Int -> IO Int) -> IO (Int, BTree RealWorld Int Int c) #-}
{-# INLINABLE modifyWithM #-}
modifyWithM :: forall m k v c. (Ord k, Prim k, Prim v, PrimMonad m)
  => Context (PrimState m) c
  -> BTree (PrimState m) k v c
  -> k
  -> (Maybe v -> m v)
  -> m (v, BTree (PrimState m) k v c)
modifyWithM (Context !degree !token !sizingRef) !root !k alter = do
  -- I believe I have been enlightened.
  !ins <- go root
  case ins of
    Ok v -> return (v,root)
    Split !rightNode newRootKey v sizing -> do
      writeNodeSize sizing 1
      newRootKeys <- newPrimArray (degree - 1)
      writePrimArray newRootKeys 0 newRootKey
      !newRootChildren <- newCompactArray token degree
      !leftNode <- compactAddGeneral token root
      writeCompactArray newRootChildren 0 leftNode
      !rightNode' <- compactAddGeneral token rightNode
      writeCompactArray newRootChildren 1 rightNode'
      -- let !newRoot = (BTree newRootSz newRootKeys (ContentsNodes newRootChildren))
      !newRoot <- mkBTree token sizing newRootKeys (ContentsNodes newRootChildren)
      !newSizing <- nextSizing token sizing
      writeMutVar sizingRef newSizing
      return (v,newRoot)
  where
  go :: BTree (PrimState m) k v c -> m (Insert (PrimState m) k v c)
  -- go BTreeUnused = error "encountered BTreeUnused" -- should not happen
  go (BTree !szRef !keys !c) = do
    !sz <- readNodeSize szRef
    case c of
      ContentsValues !values -> do
        !e <- findIndex keys k sz
        case e of
          Left !gtIx -> do
            !v <- alter Nothing
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
                !newTree <- mkBTree token rightSzRef rightKeys (ContentsValues rightValues)
                return (Split newTree propagated v newSizing)
          Right ix -> do
            !v <- readPrimArray values ix
            !v' <- alter (Just v)
            writePrimArray values ix v'
            return (Ok v')
      ContentsNodes nodes -> do
        !(!gtIx,!isEq) <- findIndexGte keys k sz
        -- case e of
        --   Right _ -> error "write Right case"
        --   Left gtIx -> do
        !node <- readCompactArray nodes (if isEq then gtIx + 1 else gtIx)
        !ins <- go node
        case ins of
          Ok !v -> return (Ok v)
          Split !rightNode !propagated !v !sizing -> if sz < degree - 1
            then do
              unsafeInsertPrimArray sz gtIx propagated keys
              unsafeInsertCompactArray (sz + 1) (gtIx + 1) rightNode nodes
              writeNodeSize szRef (sz + 1)
              writeMutVar sizingRef sizing
              return (Ok v)
            else do
              let !middleIx = div sz 2
                  !leftKeys = keys
                  !leftNodes = nodes
                  !rightSzRef = sizing
              !middleKey <- readPrimArray keys middleIx
              !rightKeys <- newPrimArray (degree - 1)
              !rightNodes <- newCompactArray token degree -- uninitializedNode
              let !leftSize = middleIx
                  !rightSize = sz - leftSize
              if middleIx >= gtIx
                then do
                  copyMutablePrimArray rightKeys 0 leftKeys (leftSize + 1) (rightSize - 1)
                  copyCompactMutableArray rightNodes 0 leftNodes (leftSize + 1) rightSize
                  unsafeInsertPrimArray leftSize gtIx propagated leftKeys
                  unsafeInsertCompactArray (leftSize + 1) (gtIx + 1) rightNode leftNodes
                  writeNodeSize szRef (leftSize + 1)
                  writeNodeSize rightSzRef (rightSize - 1)
                else do
                  -- Currently, we're copying from left to right and
                  -- then doing another copy from right to right. We can do better.
                  -- There is a similar note further up.
                  copyMutablePrimArray rightKeys 0 leftKeys (leftSize + 1) (rightSize - 1)
                  copyCompactMutableArray rightNodes 0 leftNodes (leftSize + 1) rightSize
                  unsafeInsertPrimArray (rightSize - 1) (gtIx - leftSize - 1) propagated rightKeys
                  unsafeInsertCompactArray rightSize (gtIx - leftSize) rightNode rightNodes
                  writeNodeSize szRef leftSize
                  writeNodeSize rightSzRef rightSize
              !newSizing <- nextSizing token rightSzRef
              !x <- mkBTree token rightSzRef rightKeys (ContentsNodes rightNodes)
              return (Split x middleKey v newSizing)

-- Preconditions:
-- * marr is sorted low to high
-- * sz is less than or equal to the true size of marr
-- The returned value is either
-- * in the inclusive range [0,sz - 1]
-- * the value (-1), indicating that no match was found
findIndex :: forall m a. (PrimMonad m, Ord a, Prim a)
  => MutablePrimArray (PrimState m) a -> a -> Int -> m (Either Int Int) -- (# Int# | Int# #)
findIndex !marr !needle !sz = go 0
  where
  go :: Int -> m (Either Int Int)
  go !i = if i < sz
    then do
      !a <- readPrimArray marr i
      case compare a needle of
        LT -> go (i + 1)
        EQ -> return (Right i)
        GT -> return (Left i)
    else return (Left i)

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

findIndexBetween :: forall m a. (PrimMonad m, Ord a, Prim a)
  => MutablePrimArray (PrimState m) a -> a -> Int -> m Int
findIndexBetween !marr !needle !sz = go 0
  where
  go :: Int -> m Int
  go !i = if i < sz
    then do
      a <- readPrimArray marr i
      if a > needle
        then return i
        else go (i + 1)
    else return i -- i should be equal to sz

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
  -> BTree (PrimState m) k v c
  -> m String
-- debugMap (Context _ _ _ _ _) BTreeUnused = return "BTreeUnused, should not happen"
debugMap (Context _ _ _) (BTree !rootSizing !rootKeys !rootContents) = do
  !rootSz <- readNodeSize rootSizing
  let go :: Int -> Int -> MutablePrimArray (PrimState m) k -> Contents (PrimState m) k v c -> m [(Int,String)]
      go level sz keys c = case c of
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
          BTree lastSizing lastKeys lastContents <- readCompactArray nodes sz
          lastSz <- readNodeSize lastSizing
          lastStrs <- go (level + 1) lastSz lastKeys lastContents
          -- return (nextStrs ++ [(level,show k)])
          return ([(level, "start")] ++ concat pairs ++ lastStrs)
  allStrs <- go 0 rootSz rootKeys rootContents
  return $ unlines $ map (\(level,str) -> replicate (level * 2) ' ' ++ str) ((0,"root size: " ++ show rootSz) : allStrs)

pairForM :: forall m a b c d. (Prim a, PrimMonad m)
  => Int 
  -> MutablePrimArray (PrimState m) a 
  -> CompactMutableArray (PrimState m) d c
  -> (a -> d c -> m b)
  -> m [b]
pairForM sz marr1 marr2 f = go 0
  where
  go :: Int -> m [b]
  go ix = if ix < sz
    then do
      a <- readPrimArray marr1 ix
      c <- readCompactArray marr2 ix
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
  -> BTree (PrimState m) k v c
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
  -> BTree (PrimState m) k v c
  -> m b
foldrWithKey f b0 (Context _ _ _) root = flip go b0 root
  where
  go :: BTree (PrimState m) k v c -> b -> m b
  -- go BTreeUnused !b = return b -- should not happen
  go (BTree sizing keys c) !b = do
    sz <- readNodeSize sizing
    case c of
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

foldrArray :: forall m a b c. (PrimMonad m)
  => Int -- ^ length of array
  -> (a c -> b -> m b)
  -> b
  -> CompactMutableArray (PrimState m) a c
  -> m b
foldrArray len f b0 arr = go (len - 1) b0
  where
  go :: Int -> b -> m b
  go !ix !b1 = if ix >= 0
    then do
      a <- readCompactArray arr ix
      b2 <- f a b1
      go (ix - 1) b2
    else return b1

