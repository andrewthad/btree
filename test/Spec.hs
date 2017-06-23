{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PartialTypeSignatures #-}

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
import Control.Monad.Trans.Class
import Data.Word
import Data.Primitive.Types
import Data.Foldable
import Data.Primitive.Compact (withToken,getSizeOfCompact)
import System.IO.Unsafe

import qualified Data.List as L
import qualified Data.List.NonEmpty as NE
import qualified BTree as B
import qualified BTree.Linear as BTL
import qualified BTree.Compact as BTC
import qualified Data.Set as S
import qualified Data.Primitive.PrimArray as P

main :: IO ()
main = do
  basicBenchmarks
  defaultMain tests

tests :: TestTree
tests = testGroup "Tests" [unitTests,properties]

properties :: TestTree
properties = testGroup "Properties" [scProps]

smallcheckTests :: 
     (forall n. (Show n, Ord n, Prim n) => Int -> [Positive n] -> Either Reason Reason)
  -> [TestTree]
smallcheckTests f = 
  [ testPropDepth 3 "small maps of degree 3, all permutations, no splitting"
      (over (series :: Series IO [Positive Int]) (f 3))
  , testPropDepth 7 "small maps of degree 3, all permutations"
      (over (series :: Series IO [Positive Int]) (f 3))
  , testPropDepth 7 "small maps of degree 4, all permutations"
      (over (series :: Series IO [Positive Int]) (f 4))
  , testPropDepth 10 "medium maps of degree 3, few permutations"
      (over doubletonSeriesA (f 3))
  , testPropDepth 10 "medium maps of degree 4, few permutations"
      (over doubletonSeriesA (f 4))
  , testPropDepth 10 "medium maps of degree 3, repeat keys likely, few permutations"
      (over doubletonSeriesB (f 3))
  , testPropDepth 10 "medium maps of degree 4, repeat keys likely, few permutations"
      (over doubletonSeriesB (f 4))
  , testPropDepth 500 "large maps of degree 3, repeat keys certain, one permutation"
      (over singletonSeriesB (f 3))
  , testPropDepth 500 "large maps of degree 6, one permutation"
      (over singletonSeriesA (f 6))
  , testPropDepth 500 "large maps of degree 7, repeat keys certain, one permutation"
      (over singletonSeriesB (f 7))
  ]

scProps :: TestTree
scProps = testGroup "smallcheck"
  [ testGroup "standard heap" (smallcheckTests ordering) 
  , testGroup "compact heap" (smallcheckTests orderingCompact)
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
  , testCase "compact b-tree can be created" $ withToken $ \token -> do
      _ <- BTC.new (BTC.Context 5 token) :: IO (BTC.BTree RealWorld Word Word _)
      return ()
  ]

testPropDepth :: Testable IO a => Int -> String -> a -> TestTree
testPropDepth n name = localOption (SmallCheckDepth n) . testProperty name

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

-- {-# INLINEABLE orderingCompact #-}
orderingCompact :: (Show n, Ord n, Prim n)
  => Int -- ^ degree of b-tree
  -> [Positive n] -- ^ values to insert
  -> Either Reason Reason
orderingCompact degree xs' = 
  let xs = map getPositive xs'
      expected = map (\x -> (x,x)) $ S.toAscList $ S.fromList xs
      (actual,layout) = runST $ withToken $ \c -> do
        let ctx = BTC.Context degree c
        m0 <- BTC.new ctx
        m1 <- foldlM (\ !m !x -> BTC.insert ctx m x x) m0 xs
        (,) <$> BTC.toAscList ctx m1 <*> BTC.debugMap ctx m1
  in if actual == expected
    then Right "good"
    else Left (notice (show expected) (show actual) layout)

notice :: String -> String -> String -> String
notice expected actual layout = concat
  [ "expected: "
  , expected
  , ", actual: "
  , actual
  , ", layout:\n"
  , layout
  ]

scanSeries :: forall m a. (a -> [a]) -> a -> Series m [a]
scanSeries f x0 = generate $ \n ->
  map toList $ concat $ take n $ iterate
    (\ys -> ys >>= \xs@(x NE.:| _) -> f x >>= \z -> [z NE.:| (toList xs)])
    [x0 NE.:| []]

doubletonSeriesA :: Series m [Positive Word16]
doubletonSeriesA = (fmap.fmap) Positive (scanSeries (\n -> [n + 9787, n + 29059]) 0)

doubletonSeriesB :: Series m [Positive Word8]
doubletonSeriesB = (fmap.fmap) Positive (scanSeries (\n -> [n + 89, n + 71]) 0)

singletonSeriesA :: Series m [Positive Word16]
singletonSeriesA = (fmap.fmap) Positive (scanSeries (\n -> [n + 26399]) 0)

singletonSeriesB :: Series m [Positive Word8]
singletonSeriesB = (fmap.fmap) Positive (scanSeries (\n -> [n + 73]) 0)

sizeAfterInserts :: Int -> Int -> IO Word 
sizeAfterInserts total degree = withToken $ \c -> do
  let ctx = BTC.Context degree c
  m0 <- BTC.new ctx
  let go !ix !m = if ix < total
        then do
          m' <- BTC.insert ctx m (ix :: Int) ix
          go (ix + 1) m'
        else return ()
  go 0 m0
  getSizeOfCompact c

sizeAfterRepeatedInserts :: Int -> IO Word 
sizeAfterRepeatedInserts total = withToken $ \c -> do
  let ctx = BTC.Context 8 c
  m0 <- BTC.new ctx
  let go !ix !m = if ix < total
        then do
          -- same key every time
          m' <- BTC.insert ctx m (99 :: Int) (ix :: Int)
          go (ix + 1) m'
        else return ()
  go 0 m0
  getSizeOfCompact c

basicBenchmarks :: IO ()
basicBenchmarks = do
  let degrees = [8,16,64,128,230]
      sizes = [1000,10000,100000]
      pairs = (,) <$> degrees <*> sizes
  forM_ pairs $ \(degree,size) -> do
    sz <- sizeAfterInserts size degree
    putStrLn ("Bytes of " ++ show size ++ " distinct inserts into b-tree of degree " ++ show degree ++ ": " ++ show sz)
  putStrLn "Repeated Inserts"
  forM_ sizes $ \size -> do
    sz <- sizeAfterRepeatedInserts size
    putStrLn ("Bytes of " ++ show size ++ " repeated inserts into b-tree: " ++ show sz)
 

