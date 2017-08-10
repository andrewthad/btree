{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

-- {-# OPTIONS_GHC -Wall -Werror -O2 #-}

module BTree.Store
  ( BTree
  , Initialize(..)
  , Deinitialize(..)
  , Decision(..)
  , new
  , free
  , with
  , with_
  , lookup
  , insert
  , modifyWithM_
  , modifyWithM
  , modifyWithPtr
  , foldrWithKey
  , toAscList
  ) where

import Prelude hiding (lookup)
import Foreign.Storable
import Foreign.Ptr
import Foreign.Marshal.Alloc hiding (free)
import Foreign.Marshal.Array
import Data.Bits
import Data.Word
import Data.Int
import GHC.Ptr (Ptr(..))
import qualified Data.Primitive.Addr as PA
import qualified Foreign.Marshal.Alloc as FMA

data BTree k v = BTree 
  !Int -- height
  !(Ptr (Node k v)) -- root node

data Node k v

class Storable a => Initialize a where
  initialize :: Ptr a -> IO ()
  -- ^ Initialize the memory at a pointer. An implementation
  --   of this function may do nothing, or if the data contains
  --   more pointers, @initialize@ may allocate additional memory.
  initializeElemOff :: Ptr a -> Int -> IO ()
  -- ^ Can be overridden for efficiency
  initializeElemOff ptr ix = do
    initialize (plusPtr ptr (ix * sizeOf (undefined :: a)) :: Ptr a)
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

class Storable a => Deinitialize a where
  deinitialize :: Ptr a -> IO ()
  deinitializeElemOff :: Ptr a -> Int -> IO ()
  -- ^ Can be overridden for efficiency
  deinitializeElemOff ptr ix =
    deinitialize (plusPtr ptr (ix * sizeOf (undefined :: a)) :: Ptr a)
  -- ^ Free any memory in the data structure pointed to.
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
  sizeOf _ = 2 * sizeOf (undefined :: Int)
  alignment _ = alignment (undefined :: Int)
  peek ptr = do
    height <- peekElemOff (castPtr ptr :: Ptr Int) 0
    root <- peekElemOff (castPtr ptr :: Ptr (Ptr (Node k v))) 1
    return (BTree height root)
  poke ptr (BTree height root) = do
    pokeElemOff (castPtr ptr :: Ptr Int) 0 height
    pokeElemOff (castPtr ptr :: Ptr (Ptr (Node k v))) 1 root

-- this instance relies on Int and Ptr being the same
-- size. this seems to be true for everything that
-- GHC targets.
--
-- This instance bypasses the check on the size of the keys
-- and values. This is not good.
instance Initialize (BTree k v) where
  initialize ptr = do
    pokeElemOff (castPtr ptr :: Ptr Int) 0 (0 :: Int)
    pokeElemOff (castPtr ptr :: Ptr (Ptr (Node k v))) 1 =<< newNode 1

instance (Storable k, Deinitialize v) => Deinitialize (BTree k v) where
  deinitialize ptr = do
    bt <- peek ptr
    free bt

newtype Uninitialized a = Uninitialized a
  deriving (Storable)

instance Storable a => Initialize (Uninitialized a) where
  initialize _ = return ()
  initializeElemOff _ _ = return ()
  initializeElems _ _ = return ()

instance Storable a => Deinitialize (Uninitialized a) where
  deinitialize _ = return ()
  deinitializeElemOff _ _ = return ()
  deinitializeElems _ _ = return ()

instance Initialize Word8 where
  initialize _ = return ()
  initializeElemOff _ _ = return ()
  initializeElems _ _ = return ()

instance Deinitialize Word8 where
  deinitialize _ = return ()
  deinitializeElemOff _ _ = return ()
  deinitializeElems _ _ = return ()

instance Initialize Word16 where
  initialize _ = return ()
  initializeElemOff _ _ = return ()
  initializeElems _ _ = return ()

instance Deinitialize Word16 where
  deinitialize _ = return ()
  deinitializeElemOff _ _ = return ()
  deinitializeElems _ _ = return ()

instance Initialize Word where
  initialize ptr = poke ptr (0 :: Word)
  initializeElemOff ptr off = pokeElemOff ptr off (0 :: Word)
  initializeElems ptr elemLen = PA.setAddr (ptrToAddr ptr) elemLen (0 :: Word)

instance Deinitialize Word where
  deinitialize _ = return ()
  deinitializeElemOff _ _ = return ()
  deinitializeElems _ _ = return ()

instance Initialize Int where
  initialize ptr = poke ptr (0 :: Int)
  initializeElemOff ptr off = pokeElemOff ptr off (0 :: Int)
  initializeElems ptr elemLen = PA.setAddr (ptrToAddr ptr) elemLen (0 :: Int)

instance Initialize Int64 where
  initialize ptr = poke ptr (0 :: Int64)
  initializeElemOff ptr off = pokeElemOff ptr off (0 :: Int64)
  initializeElems ptr elemLen = PA.setAddr (ptrToAddr ptr) elemLen (0 :: Int64)

ptrToAddr :: Ptr a -> PA.Addr
ptrToAddr (Ptr x) = PA.Addr x

instance Initialize Word32 where
  initialize ptr = poke ptr (0 :: Word32)

instance Deinitialize Word32 where
  deinitialize _ = return ()
  deinitializeElemOff _ _ = return ()
  deinitializeElems _ _ = return ()

instance Deinitialize Int where
  deinitialize _ = return ()
  deinitializeElemOff _ _ = return ()
  deinitializeElems _ _ = return ()

instance Deinitialize Int64 where
  deinitialize _ = return ()
  deinitializeElemOff _ _ = return ()
  deinitializeElems _ _ = return ()

instance Initialize Char where
  initialize _ = return ()
  initializeElemOff _ _ = return ()
  initializeElems _ _ = return ()

instance Deinitialize Char where
  deinitialize _ = return ()
  deinitializeElemOff _ _ = return ()
  deinitializeElems _ _ = return ()


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
  if childDegree < minimumDegree
    then fail $ "Btree.new: child degree cannot be less than " ++ show minimumDegree
    else return ()
  if branchDegree < minimumDegree
    then fail $ "Btree.new: branch degree cannot be less than " ++ show minimumDegree
    else return ()
  ptr <- newNode 0
  return (BTree 0 ptr)

minimumDegree :: Int
minimumDegree = 6

-- | Release all memory allocated by the b-tree. Do not attempt
--   to use the b-tree after calling this.
free :: forall k v. (Storable k, Deinitialize v) => BTree k v -> IO ()
free (BTree height root) = go height root
  where
  branchDegree :: Int
  !branchDegree = calcBranchDegree root
  childDegree :: Int
  !childDegree = calcChildDegree root
  go :: Int -> Ptr (Node k v) -> IO ()
  go n ptrNode = if n > 0
    then do
      sz <- readNodeSize ptrNode
      let KeysNodes _ nodes = readNodeKeysNodes branchDegree ptrNode
      arrMapM_ (go (n - 1)) (sz + 1) nodes
      FMA.free ptrNode
    else do
      sz <- readNodeSize ptrNode
      let KeysValues _ values = readNodeKeysValues childDegree ptrNode
      deinitializeElems (getArr values) sz
      FMA.free ptrNode

with :: (Storable k, Initialize v, Deinitialize v) => (BTree k v -> IO (a, BTree k v)) -> IO a
with f = do
  initial <- new
  (a,final) <- f initial
  free final
  return a

with_ :: (Storable k, Initialize v, Deinitialize v) => (BTree k v -> IO (BTree k v)) -> IO ()
with_ f = do
  initial <- new
  final <- f initial
  free final

newNode :: 
     Int -- ^ initial size, if you pick something greater than 0,
         --   you need to write to those indices after calling this.
  -> IO (Ptr (Node k v))
newNode n = do
  -- We would really like to ensure that this is aligned to a
  -- 4k boundary, but malloc does not guarentee this. I think
  -- that posix_memalign should work, but whatever.
  ptr <- mallocBytes maxSize
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
maxSize = 4096 - 2 * sizeOf (undefined :: Int)
-- maxSize = 200

-- not actually sure if this is really correct.
calcBranchDegree :: forall k v. (Storable k, Storable v) => Ptr (Node k v) -> Int
calcBranchDegree _ = calcBranchDegreeInt (sizeOf (undefined :: k)) (alignment (undefined :: k))

calcBranchDegreeInt :: Int -> Int -> Int
calcBranchDegreeInt keySz keyAlignment = 
  let space = maxSize - max (sizeOf (undefined :: Int)) keyAlignment - sizeOf (undefined :: Ptr a)
      allowedNodes = quot space (sizeOf (undefined :: Ptr a) + keySz)
   in allowedNodes

-- not actually sure if this is really correct. need to think about this math
-- a little more. Or I guess I could write something that does a brute force
-- consideration of all the possible sizes and alignment. That would convince me.
calcChildDegree :: forall k v. (Storable k, Storable v) => Ptr (Node k v) -> Int
calcChildDegree _ = calcChildDegreeInt
  (sizeOf (undefined :: k))
  (alignment (undefined :: k))
  (sizeOf (undefined :: v))

calcChildDegreeInt :: Int -> Int -> Int -> Int
calcChildDegreeInt keySz keyAlignment valueSz = 
  let space = maxSize - max (sizeOf (undefined :: Int)) keyAlignment - valueSz
      allowedValues = quot space (valueSz + keySz)
   in allowedValues + 1 -- add one because of the meaning we assign to degree

{-# INLINABLE lookup #-}
-- {-# SPECIALIZE lookup :: BTree Int Int -> Int -> IO (Maybe Int) #-}
-- {-# SPECIALIZE lookup :: BTree Int64 Int -> Int64 -> IO (Maybe Int) #-}
-- {-# SPECIALIZE lookup :: BTree Word32 Int -> Word32 -> IO (Maybe Int) #-}
-- {-# SPECIALIZE lookup :: BTree Word16 Int -> Word16 -> IO (Maybe Int) #-}
lookup :: forall k v. (Ord k, Storable k, Storable v)
  => BTree k v -> k -> IO (Maybe v)
lookup (BTree height rootNode) k = go height rootNode
  where
  branchDegree :: Int
  !branchDegree = calcBranchDegree rootNode
  childDegree :: Int
  childDegree = calcChildDegree rootNode
  go :: Int -> Ptr (Node k v) -> IO (Maybe v)
  go !n !ptrNode = if n > 0
    then do
      !sz <- readNodeSize ptrNode
      let !(KeysNodes keys nodes) = readNodeKeysNodes branchDegree ptrNode
      !ix <- findIndexOfGtElem keys k sz
      !node <- readArr nodes ix
      go (n - 1) node
    else do
      !sz <- readNodeSize ptrNode
      let !(KeysValues keys values) = readNodeKeysValues childDegree ptrNode
      !ix <- findIndex keys k sz
      if ix < 0
        then return Nothing
        else do
          !v <- readArr values ix
          return (Just v)

data Insert k v r
  = Ok !r
  | Split !(Ptr (Node k v)) !k !r
    -- The new node that will go to the right,
    -- the key propagated to the parent,
    -- the inserted value
  | TooSmall !r
  | TotallyEmpty !(Ptr (Node k v)) !r
    -- The node has zero keys left. Its sole child
    -- is provided.

{-# INLINE insert #-}
insert :: (Ord k, Storable k, Initialize v)
  => BTree k v
  -> k
  -> v
  -> IO (BTree k v)
insert !m !k !v = do
  !(!(),!node) <- modifyWithPtr m k
    (Right (\ptr ix -> pokeElemOff ptr ix v))
    (\ptr ix -> pokeElemOff ptr ix v >> return ((),Keep))
  return node

-- delete :: (Ord k, Storable k, Regioned v)
--   => BTree k v
--   -> k
--   -> IO (BTree k v)
-- delete !m !k = do
--   !(!(),!node) <- modifyWithPtr m k
--     (Left ())
--     (\_ _ -> return ((),Delete))
--   return node

data Decision = Keep | Delete

-- data Position = Next | Prev

modifyWithM_ :: forall k v. (Ord k, Storable k, Initialize v)
  => BTree k v 
  -> k
  -> (v -> IO v) -- ^ value modification, happens for newly inserted elements and for previously existing elements
  -> IO (BTree k v)
modifyWithM_ bt k alter = do
  (_, bt') <- modifyWithPtr bt k
    (Right (\ptr ix -> peekElemOff ptr ix >>= alter >>= pokeElemOff ptr ix))
    (\ptr ix -> peekElemOff ptr ix >>= alter >>= pokeElemOff ptr ix >>= \_ -> return ((),Keep))
  return bt'

modifyWithM :: forall k v a. (Ord k, Storable k, Initialize v)
  => BTree k v 
  -> k
  -> (v -> IO (a, v)) -- ^ value modification, happens for newly inserted elements and for previously existing elements
  -> IO (a, BTree k v)
modifyWithM bt k alter = do
  (a, bt') <- modifyWithPtr bt k
    (Right (\ptr ix -> do
      (a,v') <- alter =<< peekElemOff ptr ix
      pokeElemOff ptr ix v'
      return a
    ))
    (\ptr ix -> do
      (a,v') <- alter =<< peekElemOff ptr ix
      pokeElemOff ptr ix v'
      return (a,Keep)
    )
  return (a,bt')

{-# INLINABLE modifyWithPtr #-}
-- {-# SPECIALIZE modifyWithPtr :: BTree Int Int -> Int -> (Either () (Ptr Int -> Int -> IO ())) -> (Ptr Int -> Int -> IO ((),Decision)) -> IO ((), BTree Int Int) #-}
-- {-# SPECIALIZE modifyWithPtr :: BTree Word32 Int -> Word32 -> (Either r (Ptr Int -> Int -> IO r)) -> (Ptr Int -> Int -> IO (r,Decision)) -> IO (r, BTree Word32 Int) #-}
-- {-# SPECIALIZE modifyWithPtr :: BTree Int64 Int -> Int64 -> (Either r (Ptr Int -> Int -> IO r)) -> (Ptr Int -> Int -> IO (r,Decision)) -> IO (r, BTree Int64 Int) #-}
modifyWithPtr :: forall k v r. (Ord k, Storable k, Initialize v)
  => BTree k v 
  -> k
  -> (Either r (Ptr v -> Int -> IO r)) -- ^ modifications to newly inserted value
  -> (Ptr v -> Int -> IO (r,Decision)) -- ^ modification to value if key is found
  -> IO (r, BTree k v)
modifyWithPtr (BTree !height !root) !k !mpostInitializeElemOff alterElemOff = do
  !ins <- go height root
  case ins of
    Ok !r -> return (r, BTree height root)
    TotallyEmpty child r -> do
      FMA.free root
      return (r, BTree (height - 1) child)
    -- if the root is too small, we do not care. The root
    -- can have any number of keys greater than 1.
    TooSmall !r -> return (r, BTree 0 root)
    Split !rightNode !newRootKey !v -> do
      newRoot <- newNode 1
      let KeysNodes keys nodes = readNodeKeysNodes branchDegree newRoot
          leftNode = root
      writeArr keys 0 newRootKey
      writeArr nodes 0 leftNode
      writeArr nodes 1 rightNode
      return (v,BTree (height + 1) newRoot)
  where
  childDegree :: Int
  !childDegree = calcChildDegree root
  branchDegree :: Int
  !branchDegree = calcBranchDegree root
  go :: Int -> Ptr (Node k v) -> IO (Insert k v r)
  go n ptrNode = if n > 0
    then do
      sz <- readNodeSize ptrNode
      let KeysNodes keys nodes = readNodeKeysNodes branchDegree ptrNode
      !gtIx <- findIndexOfGtElem keys k sz
      !node <- readArr nodes gtIx
      !ins <- go (n - 1) node
      case ins of
        Ok !r -> return (Ok r)
        TotallyEmpty _ _ -> fail "TotallyEmpty: handle this in go"
        TooSmall !r -> do
          if n == 1
            then 
              if | gtIx >= sz -> do
                     if (gtIx /= sz) then fail "bad logic found: gtIx must be sz" else return ()
                     childSz <- readNodeSize node
                     let KeysValues childKeys childValues = readNodeKeysValues childDegree node
                     prevPtrNode <- readArr nodes (gtIx - 1)
                     prevSz <- readNodeSize prevPtrNode
                     let KeysValues prevKeys prevValues = readNodeKeysValues childDegree prevPtrNode
                     if childSz + prevSz < childDegree
                       then do
                         mergeIntoLeft prevKeys prevValues prevSz childKeys childValues childSz
                         writeNodeSize prevPtrNode (childSz + prevSz)
                         FMA.free node
                         if sz < 2
                           then do
                             -- whatever code handles this one level up needs
                             -- to remember to call free on the now-obsolete
                             -- branch node. 
                             return (TotallyEmpty prevPtrNode r)
                           else do
                             -- putStrLn $ "size of nodes: " ++ show sz
                             _ <- fail "merging arrays"
                             removeArr sz (sz - 1) keys -- first key
                             removeArr (sz + 1) sz nodes -- right child of first key
                             writeNodeSize ptrNode (sz - 1)
                             continue
                       else do
                         -- putStrLn $ "child size: " ++ show childSz
                         -- putStrLn $ "next size: " ++ show nextSz
                         (newPrevSz,newChildSz) <- balanceArrays prevKeys prevValues prevSz childKeys childValues childSz
                         writeNodeSize prevPtrNode newPrevSz
                         writeNodeSize node newChildSz
                         readArr childKeys 0 >>= writeArr keys (sz - 1)
                         continue
                 | gtIx > 0 -> fail "write me now"
                     -- childSz <- readNodeSize node
                     -- let KeysValues childKeys childValues = readNodeKeysValues childDegree node
                     -- nextPtrNode <- readArr nodes (gtIx + 1)
                     -- nextSz <- readNodeSize nextPtrNode
                     -- let KeysValues nextKeys nextValues = readNodeKeysValues childDegree nextPtrNode
                     -- prevPtrNode <- readArr nodes (gtIx - 1)
                     -- prevSz <- readNodeSize prevPtrNode
                     -- let KeysValues prevKeys prevValues = readNodeKeysValues childDegree prevPtrNode
                     -- if nextSz > prevSz
                     --   then runNext 
                     --   else runPrev
                 | otherwise -> do -- gtIx must be 0
                     if (gtIx /= 0) then fail "bad logic found" else return ()
                     childSz <- readNodeSize node
                     let KeysValues childKeys childValues = readNodeKeysValues childDegree node
                     nextPtrNode <- readArr nodes 1
                     nextSz <- readNodeSize nextPtrNode
                     let KeysValues nextKeys nextValues = readNodeKeysValues childDegree nextPtrNode
                     if childSz + nextSz < childDegree
                       then do
                         mergeIntoLeft childKeys childValues childSz nextKeys nextValues nextSz
                         writeNodeSize node (childSz + nextSz)
                         FMA.free nextPtrNode
                         -- _ <- fail "after call free"
                         if sz < 2
                           then do
                             -- whatever code handles this one level up needs
                             -- to remember to call free on the now-obsolete
                             -- branch node. 
                             return (TotallyEmpty node r)
                           else do
                             -- putStrLn $ "size of nodes: " ++ show sz
                             _ <- fail "merging arrays"
                             removeArr sz 0 keys -- first key
                             removeArr (sz + 1) 1 nodes -- right child of first key
                             writeNodeSize ptrNode (sz - 1)
                             continue
                       else do
                         -- putStrLn $ "child size: " ++ show childSz
                         -- putStrLn $ "next size: " ++ show nextSz
                         _ <- fail "balancing arrays"
                         (newChildSz,newNextSz) <- balanceArrays childKeys childValues childSz nextKeys nextValues nextSz
                         writeNodeSize nextPtrNode newNextSz
                         writeNodeSize node newChildSz
                         readArr nextKeys 0 >>= writeArr keys 0
                         continue
            else fail "write code for branch handling a branch merge"
          where
          continue :: IO (Insert k v r)
          continue = do
            newSz <- readNodeSize ptrNode
            let minimumBranchSz = half branchDegree - 1
            if newSz < minimumBranchSz
              then return (TooSmall r)
              else return (Ok r)
          -- runNext :: Position -> Int -> Ptr (Node k v) -> Int -> IO (Insert k v r)
          -- runNext _pos _keyIx _neighborPtrNode _neighborSz = fail "write runNext"
            -- childSz <- readNodeSize node
            -- let KeysValues childKeys childValues = readNodeKeysValues childDegree node
            -- let KeysValues neighborKeys neighborValues = readNodeKeysValues childDegree neighborPtrNode
            -- let preservedPtr = case pos of
            --       Next -> node
            --       Prev -> neighborPtrNode
            -- let destroyedPtr = case pos of
            --       Next -> neighborPtrNode
            --       Prev -> node
            -- let destroyedPtrIx = case pos of
            --       Next -> neighborIx - 1
            --       Prev -> neighborIx
            -- if childSz + nextSz < childDegree
            --   then do
            --     case pos of
            --       Next -> mergeIntoLeft childKeys childValues childSz neighborKeys neighborValues neighborSz
            --       Prev -> mergeIntoLeft neighborKeys neighborValues neighborSz childKeys childValues childSz
            --     writeNodeSize preservedPtr (childSz + neighborSz)
            --     FMA.free destroyedPtr
            --     -- _ <- fail "after call free"
            --     if sz < 2
            --       then return (TotallyEmpty preservedPtr r)
            --       else do
            --         -- putStrLn $ "size of nodes: " ++ show sz
            --         _ <- fail "merging arrays"
            --         removeArr sz 0 keys -- first key
            --         removeArr (sz + 1) 1 nodes -- right child of first key
            --         writeNodeSize ptrNode (sz - 1)
            --         continue
            --   else do
            --     -- putStrLn $ "child size: " ++ show childSz
            --     -- putStrLn $ "next size: " ++ show nextSz
            --     _ <- fail "balancing arrays"
            --     (newChildSz,newNextSz) <- balanceArrays childKeys childValues childSz nextKeys nextValues nextSz
            --     writeNodeSize nextPtrNode newNextSz
            --     writeNodeSize node newChildSz
            --     readArr nextKeys 0 >>= writeArr keys 0
            --     continue
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
      let !(KeysValues !keys !values) = readNodeKeysValues childDegree ptrNode
      !ix <- findIndex keys k sz
      if ix < 0
        then case mpostInitializeElemOff of
          Left r -> return (Ok r)
          Right postInitializeElemOff -> do
            let !gtIx = decodeGtIndex ix
            if sz < childDegree - 1
              then do
                -- We have enough space
                insertArr sz gtIx k keys
                r <- insertInitArr sz gtIx values $ \thePtr theIx -> do
                  initializeElemOff thePtr theIx
                  postInitializeElemOff thePtr theIx
                writeNodeSize ptrNode (sz + 1)
                return (Ok r)
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
                r <- if gtIx < leftSize
                  then do
                    copyArr rightKeys 0 leftKeys leftSize rightSize
                    copyArr rightValues 0 leftValues leftSize rightSize
                    insertArr leftSize gtIx k leftKeys
                    insertInitArr leftSize gtIx leftValues $ \thePtr theIx -> do
                      initializeElemOff thePtr theIx
                      postInitializeElemOff thePtr theIx
                  else do
                    -- Currently, we're copying from left to right and
                    -- then doing another copy from right to right. We
                    -- might be able to do better. We could do the same number
                    -- of memcpys but copy fewer total elements and not
                    -- have the slowdown caused by overlap.
                    copyArr rightKeys 0 leftKeys leftSize rightSize
                    copyArr rightValues 0 leftValues leftSize rightSize
                    insertArr rightSize (gtIx - leftSize) k rightKeys
                    insertInitArr rightSize (gtIx - leftSize) rightValues $ \thePtr theIx -> do
                      initializeElemOff thePtr theIx
                      postInitializeElemOff thePtr theIx
                !propagated <- readArr rightKeys 0
                return (Split newNodePtr propagated r)
        else do
          -- The key was already present in this leaf node
          !(r,dec) <- alterElemOff (getArr values) ix
          case dec of
            Keep -> return (Ok r)
            Delete -> fail "write the delete code for b tree" -- do
              -- let newSize = sz - 1
              --     minimumChildSz = half childDegree
              -- writeNodeSize ptrNode newSize
              -- removeArr sz ix keys
              -- removeArrDeinit sz ix values
              -- if newSize < minimumChildSz
              --   then return (TooSmall r)
              --   else return (Ok r)

-- this is used when one of the arrays is too small. The
-- caller of this function must ensure in advance that
-- the arrays will end up being appropriately sized
-- after the balancing.
balanceArrays :: (Storable k, Storable v) => Arr k -> Arr v -> Int -> Arr k -> Arr v -> Int -> IO (Int,Int)
balanceArrays arrA valA szA arrB valB szB = do
  let newSzA = half (szA + szB)
      newSzB = szA + szB - newSzA
      deltaA = newSzA - szA
      deltaB = negate deltaA
  if deltaA > 0 
    then do
      copyArr arrA szA arrB 0 deltaA
      copyArr arrB 0 arrB deltaA (szB - deltaA)
      copyArr valA szA valB 0 deltaA
      copyArr valB 0 valB deltaA (szB - deltaA)
    else do
      copyArr arrB deltaB arrB 0 szB
      copyArr arrB 0 arrA (szA - deltaB) deltaB
      copyArr valB deltaB valB 0 szB
      copyArr valB 0 valA (szA - deltaB) deltaB
  return (newSzA,newSzB)

-- After this operation, all of the values are in the first
-- provided array. The second one should be considered unusable
-- and it should be freed from memory soon.
mergeIntoLeft :: (Storable k, Storable v)
  => Arr k -> Arr v -> Int -> Arr k -> Arr v -> Int -> IO ()
mergeIntoLeft arrA valA szA arrB valB szB = do
  copyArr arrA szA arrB 0 szB
  copyArr valA szA valB 0 szB

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

-- {-# INLINE removeArrDeinit #-}
-- removeArrDeinit :: Deinitialize a
--   => Int -- ^ Size of the original array
--   -> Int -- ^ Index
--   -> Arr a -- ^ Array to modify
--   -> IO ()
-- removeArrDeinit !sz !i !arr = do
--   deinitializeElemOff (getArr arr) i
--   copyArr arr i arr (i + 1) (sz - i - 1)

{-# INLINE removeArr #-}
removeArr :: Storable a
  => Int -- ^ Size of the original array
  -> Int -- ^ Index
  -> Arr a -- ^ Array to modify
  -> IO ()
removeArr !sz !i !arr = do
  copyArr arr i arr (i + 1) (sz - i - 1)

{-# INLINE insertInitArr #-}
insertInitArr :: forall a r. Storable a
  => Int -- ^ Size of the original array
  -> Int -- ^ Index
  -> Arr a -- ^ Array to modify
  -> (Ptr a -> Int -> IO r)
  -> IO r
insertInitArr !sz !i !arr@(Arr ptr0) f = do
  copyArr arr (i + 1) arr i (sz - i)
  f ptr0 i

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
--   typically useful in production code.
toAscList :: forall k v. (Ord k, Storable k, Storable v)
  => BTree k v
  -> IO [(k,v)]
toAscList = foldrWithKey f []
  where
  f :: k -> v -> [(k,v)] -> IO [(k,v)]
  f k v xs = return ((k,v) : xs)
