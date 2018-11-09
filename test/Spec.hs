{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE LambdaCase #-}

{-# OPTIONS_GHC -Wno-partial-type-signatures #-}

import Test.Tasty
import Test.Tasty.SmallCheck as SC
import Test.SmallCheck.Series
import Test.Tasty.HUnit
import Data.List
import Data.Ord
import Control.Monad
import Control.Monad.ST
import Debug.Trace
import Control.Monad.Trans.Except
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.Class
import Data.Word
import Data.Int
import Data.Proxy
import Data.Primitive.Types
import Data.Foldable
import System.IO.Unsafe
import Data.Hashable
import Foreign.Storable
import GHC.TypeLits
import Foreign.Ptr
import Control.Monad.Random.Strict hiding (fromList)
import Data.Bifunctor
import GHC.Exts (fromList)
import Control.Monad.ST (ST, runST)

import qualified Data.List as L
import qualified Data.List.NonEmpty as NE
import qualified BTree as B
import qualified BTree.Linear as BTL
import qualified BTree.Store as BTS
import qualified Data.Set as S
import qualified Data.Primitive.PrimArray as P

singletonPrimArray :: forall a. Prim a => a -> P.PrimArray a
singletonPrimArray x = runST sing where
  sing :: forall s. ST s (P.PrimArray a)
  sing = do
    arr <- P.newPrimArray 1
    P.writePrimArray arr 0 x
    P.unsafeFreezePrimArray arr

main :: IO ()
main = do
  putStrLn "Starting test suite"
  BTS.with_ $ \bt0 -> do
    bt1 <- BTS.modifyWithM_ bt0 (4 :: Int) $ \bti0 -> do
      bti1 <- BTS.insert bti0 'x' (7 :: Int)
      bti2 <- BTS.insert bti1 'z' (7 :: Int)
      bti3 <- BTS.insert bti2 'y' (7 :: Int)
      return bti3
    bt2 <- BTS.modifyWithM_ bt1 (2 :: Int) $ \bti0 -> do
      bti1 <- BTS.insert bti0 'a' (7 :: Int)
      bti2 <- BTS.insert bti1 'b' (7 :: Int)
      bti3 <- BTS.insert bti2 'c' (7 :: Int)
      return bti3
    mint <- runMaybeT $ do
      bti <- MaybeT (BTS.lookup bt2 4)
      MaybeT (BTS.lookup bti 'x')
    print mint
    return bt2
    -- BTS.toAscList bt2 >>= print 
  -- BTS.with_ $ \bt0 -> do
  --   bt1 <- BTS.insert bt0 (4 :: Int) 'x'
  --   bt2 <- BTS.insert bt1 3 'z'
  --   BTS.toAscList bt2 >>= print 
  --   return bt2
  defaultMain tests
  -- basicBenchmarks
  putStrLn "Finished test suite"

tests :: TestTree
tests = testGroup "Tests" [unitTests,properties]

properties :: TestTree
properties = testGroup "Properties" [scProps]

smallcheckTests :: 
     (forall x. (Hashable x, Show x, Ord x, Eq x, BTS.Initialize x, BTS.Deinitialize x, Bounded x, Integral x) => [x] -> Either Reason Reason)
  -> [TestTree]
smallcheckTests f = 
  [ testPropDepth 3 "small maps with 256 bit keys and values, all permutations, no splitting"
      (over (series :: Series IO [Padded 256]) f)
  , testPropDepth 4 "small maps of degree 3, all permutations, one split"
      (over (series :: Series IO [Padded 256]) f)
  , testPropDepth 7 "small maps of degree 3, all permutations"
      (over (series :: Series IO [Padded 256]) f)
  , testPropDepth 7 "small maps of degree 4, all permutations"
      (over (series :: Series IO [Padded 256]) f)
  , testPropDepth 10 "medium maps of degree 3, few permutations"
      (over (doubletonSeriesA (Proxy :: Proxy 256)) f)
  , testPropDepth 10 "medium maps of degree 4, few permutations"
      (over (doubletonSeriesA (Proxy :: Proxy 256)) f)
  , testPropDepth 10 "medium maps of degree 3, repeat keys likely, few permutations"
      (over (doubletonSeriesB (Proxy :: Proxy 256)) f)
  , testPropDepth 10 "medium maps of degree 4, repeat keys likely, few permutations"
      (over (doubletonSeriesB (Proxy :: Proxy 256)) f)
  , testPropDepth 150 "large maps of degree 3, repeat keys certain, one permutation"
      (over (singletonSeriesB (Proxy :: Proxy 256)) f)
  , testPropDepth 150 "large maps of degree 6, one permutation"
      (over (singletonSeriesA (Proxy :: Proxy 128)) f)
  , testPropDepth 150 "large maps of degree 7, repeat keys certain, one permutation"
      (over (singletonSeriesB (Proxy :: Proxy 128)) f)
  , testPropDepth 200 "large maps" (over word32Series f)
  -- , testPropDepth 1050 "large maps with Word16" (over word16SeriesSingles f)
  ]

scProps :: TestTree
scProps = testGroup "smallcheck"
  [ testGroup "unmanaged heap" (smallcheckTests orderingStorable)
  , testGroup "unmanaged heap nested" (smallcheckTests orderingNested)
  -- the diverse ones take too long to run
  -- , testGroup "unmanaged heap nested diverse" (smallcheckTests orderingNestedDiverse)
  -- deletion does not work yet
  -- , testGroup "unmanaged heap deletions" (smallcheckTests deletionStorable)
  ]

unitTests :: TestTree
unitTests = testGroup "Unit tests"
  [ testCase "put followed by get (tests lookup,insert,toAscList)" $ do
      let xs = [1,3,2,4,6,5 :: Word]
          xs' = map (\x -> (x,x)) xs
          e = runST $ runExceptT $ do
            b <- lift $ B.fromList (B.Context (BTL.Context 20)) xs'
            forM_ xs $ \k -> do
              mv <- lift $ B.lookup b k
              case mv of
                Nothing -> do
                  flattened <- lift (B.toAscList b)
                  ExceptT $ return $ Left $ concat
                    [ "key "
                    , show k
                    , " was not found. Flattened tree: "
                    , show flattened
                    ]
                Just v -> if v == k
                  then return ()
                  else do
                    flattened <- lift (B.toAscList b)
                    ExceptT $ return $ Left $ concat
                      [ "key "
                      , show k 
                      , " was found with non-matching value "
                      , show v
                      , ". Flattened tree: "
                      , show flattened
                      ]
      case e of
        Left err -> assertFailure err
        Right () -> return ()
  , testCase "insertions are sorted" $ do
      let xs = [1,3,2,4,6,5,19,11,7 :: Word]
          xs' = map (\x -> (x,x)) xs
      actual <- return (runST (B.fromList (B.Context (BTL.Context 4)) xs' >>= B.toAscList))
      actual @?= S.toAscList (S.fromList xs')
  ]

testPropDepth :: Testable IO a => Int -> String -> a -> TestTree
testPropDepth n name = localOption (SmallCheckDepth n) . testProperty name

lookupAfterInsert :: (Show n, Ord n, Prim n)
  => Int -- ^ degree of b-tree
  -> [Positive n] -- ^ values to insert
  -> Either Reason Reason
lookupAfterInsert degree xs' =
  let xs = map getPositive xs'
      expected = map (\x -> (x,x)) $ S.toAscList $ S.fromList xs
   in fmap (const "good") $ runST $ do
        m <- B.new (B.Context (BTL.Context degree))
        forM_ xs $ \x -> do
          B.insert m x x
        r1 <- foldlM (\e x -> case e of
            Right () -> do
              B.lookup m x >>= \case
                Nothing -> return $ Left ("could not find " ++ show x ++ " after inserting it")
                Just y -> return $ if x == y
                  then Right ()
                  else Left ("looked up " ++ show x ++ " but found wrong value " ++ show y)
            Left err -> return (Left err)
          ) (Right ()) xs
        r2 <- runExceptT $ forM_ xs $ \x -> lift (B.lookup m x) >>= \case
          Nothing -> ExceptT $ return $ Left ("could not find " ++ show x ++ " after inserting it")
          Just y -> ExceptT $ return $ if x == y
            then Right ()
            else Left ("looked up " ++ show x ++ " but found wrong value " ++ show y)
        return (r1 >> r2)

lookupAfterInsertUnmanaged :: (Show n, Ord n, BTS.Initialize n, BTS.Deinitialize n)
  => Int -- ^ degree of b-tree
  -> [Positive n] -- ^ values to insert
  -> Either Reason Reason
lookupAfterInsertUnmanaged degree xs' =
  let xs = map getPositive xs'
      expected = map (\x -> (x,x)) $ S.toAscList $ S.fromList xs
   in fmap (const "good") $ unsafePerformIO $ BTS.with $ \m0 -> do
        m1 <- foldlM (\ !m !x -> BTS.insert m x x) m0 xs
        r1 <- foldlM (\e x -> case e of
            Right () -> do
              BTS.lookup m1 x >>= \case
                Nothing -> return $ Left ("could not find " ++ show x ++ " after inserting it")
                Just y -> return $ if x == y
                  then Right ()
                  else Left ("looked up " ++ show x ++ " but found wrong value " ++ show y)
            Left err -> return (Left err)
          ) (Right ()) xs
        r2 <- runExceptT $ forM_ xs $ \x -> lift (BTS.lookup m1 x) >>= \case
          Nothing -> ExceptT $ return $ Left ("could not find " ++ show x ++ " after inserting it")
          Just y -> ExceptT $ return $ if x == y
            then Right ()
            else Left ("looked up " ++ show x ++ " but found wrong value " ++ show y)
        return (r1 >> r2, m1)


ordering :: (Show n, Ord n, Prim n)
  => Int -- ^ degree of b-tree
  -> [Positive n] -- ^ values to insert
  -> Either Reason Reason
ordering degree xs' = 
  let xs = map getPositive xs'
      expected = map (\x -> (x,x)) $ S.toAscList $ S.fromList xs
      (actual,layout) = runST $ do
        m <- B.new (B.Context (BTL.Context degree))
        forM_ xs $ \x -> do
          B.insert m x x
        (,) <$> B.toAscList m <*> B.debugMap m
  in if actual == expected
    then Right "good"
    else Left (notice (show expected) (show actual) layout)

orderingStorable :: (Hashable x, Show x, Eq x, Ord x, Storable x, BTS.Initialize x, BTS.Deinitialize x)
  => [x] -- ^ values to insert
  -> Either Reason Reason
orderingStorable xs = 
  let expected = map (\x -> (x,x)) $ S.toAscList $ S.fromList xs
      result = unsafePerformIO $ BTS.with $ \m0 -> do
        m1 <- foldlM (\ !m !x -> BTS.insert m x x) m0 xs
        actual <- BTS.toAscList m1
        let e = if actual == expected
              then Right "good"
              else Left (notice (show expected) (show actual) "layout not available")
        return (e,m1)
   in result

-- let us begin the most dangerous game.
orderingNested :: (Bounded x, Integral x, Hashable x, Show x, Eq x, Ord x, Storable x, BTS.Initialize x, BTS.Deinitialize x)
  => [x] -- ^ values to insert
  -> Either Reason Reason
orderingNested xs = 
  let e = unsafePerformIO $ BTS.with $ \m0 -> do
        m1 <- foldlM
          (\ !mtop !x -> do
            let subValues = take 10 (iterate (fromIntegral . hashWithSalt 13 . (+ div maxBound 3)) x)
            foldM 
              ( \ !m !y -> BTS.modifyWithM_ m x $ \mbottom ->
                  BTS.insert mbottom y y
              ) mtop subValues
          ) m0 xs
        e <- runExceptT $ forM_ xs $ \x -> do
          m <- lift $ BTS.lookup m1 x 
          case m of
            Nothing -> ExceptT (return (Left ("could not find " ++ show x ++ " in top b-tree")))
            Just b -> do
              n <- lift $ BTS.lookup b x
              case n of
                Nothing -> ExceptT (return (Left ("could not find " ++ show x ++ " in bottom b-tree")))
                Just k -> return ()
        return (e,m1)
   in fmap (const "good") e

orderingNestedDiverse :: (Bounded x, Integral x, Hashable x, Show x, Eq x, Ord x, Storable x, BTS.Initialize x, BTS.Deinitialize x)
  => [x] -- ^ values to insert
  -> Either Reason Reason
orderingNestedDiverse xs = 
  let e = unsafePerformIO $ BTS.with $ \m0 -> do
        let topSub = 600 :: Word32
            subValues = enumFromTo 0 topSub
        m1 <- foldlM
          (\ !mtop !x -> do
            foldM 
              ( \ !m !y -> BTS.modifyWithM_ m x $ \mbottom ->
                  BTS.insert mbottom y y
              ) mtop subValues
          ) m0 xs
        e <- runExceptT $ forM_ xs $ \x -> do
          m <- lift $ BTS.lookup m1 x 
          case m of
            Nothing -> ExceptT (return (Left ("could not find " ++ show x ++ " in top b-tree")))
            Just b -> do
              n <- lift $ BTS.lookup b topSub
              case n of
                Nothing -> ExceptT (return (Left ("could not find " ++ show x ++ " in bottom b-tree")))
                Just k -> return ()
        return (e,m1)
   in fmap (const "good") e

notice :: String -> String -> String -> String
notice expected actual layout = concat
  [ "expected: "
  , expected
  , ",\n actual: "
  , actual
  , ", layout:\n"
  , layout
  ]

scanSeries :: forall m a. (a -> [a]) -> a -> Series m [a]
scanSeries f x0 = generate $ \n ->
  map toList $ concat $ take n $ iterate
    (\ys -> ys >>= \xs@(x NE.:| _) -> f x >>= \z -> [z NE.:| (toList xs)])
    [x0 NE.:| []]

doubletonSeriesA :: Proxy n -> Series m [Padded n]
doubletonSeriesA _ = (fmap.fmap) Padded (scanSeries (\n -> [n + 9787, n + 29059]) 0)

doubletonSeriesB :: Proxy n -> Series m [Padded n]
doubletonSeriesB _ = (fmap.fmap) Padded (scanSeries (\n -> [n + 89, n + 71]) 0)

singletonSeriesA :: Proxy n -> Series m [Padded n]
singletonSeriesA _ = (fmap.fmap) Padded (scanSeries (\n -> [n + 26399]) 0)

singletonSeriesB :: Proxy n -> Series m [Padded n]
singletonSeriesB _ = (fmap.fmap) Padded (scanSeries (\n -> [n + 73]) 0)

word16Series :: Series m [Word16]
word16Series = (scanSeries (\n -> [n + 89, n + 71]) 0)

word32Series :: Series m [Word32]
word32Series = (scanSeries (\n -> [n + 73]) 0)

word16SeriesSingles :: Series m [Word16]
word16SeriesSingles = (scanSeries (\n -> [n + 73]) 0)

word32SeriesAlt :: Series m [Word32]
word32SeriesAlt = (scanSeries (\n -> [n + 73, n + 89]) 0)

newtype Padded (n :: Nat) = Padded Word
  deriving (Eq,Ord,Bounded,Hashable,Integral,Real,Num,Enum)

instance KnownNat n => Storable (Padded n) where
  sizeOf _ = fromInteger (natVal (Proxy :: Proxy n))
  alignment _ = fromInteger (natVal (Proxy :: Proxy n))
  peek ptr = fmap Padded (peek (castPtr ptr))
  poke ptr (Padded w) = poke (castPtr ptr) w

instance KnownNat n => BTS.Initialize (Padded n) where
  initialize _ = return ()

instance KnownNat n => BTS.Deinitialize (Padded n) where
  deinitialize _ = return ()

instance Show (Padded n) where
  show (Padded w) = show w

instance Monad m => Serial m (Padded n) where
  series = fmap (\(Positive n) -> Padded (intToWord n)) series

intToWord :: Int -> Word
intToWord = fromIntegral

deterministicShuffle :: Hashable a => [a] -> [a]
deterministicShuffle xs = evalRand (shuffle xs) (mkStdGen (hash xs))

shuffle :: [a] -> Rand StdGen [a]
shuffle [] = return []
shuffle xs = do
  randomPosition <- getRandomR (0, length xs - 1)
  let (left, (a:right)) = splitAt randomPosition xs
  fmap (a:) (shuffle (left ++ right))

