{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}

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

import qualified Data.List as L
import qualified Data.List.NonEmpty as NE
import qualified Map.Mutable.BTree.Prim as B
import qualified Data.Set as S
import qualified Data.Primitive.PrimArray as P

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "Tests" [unitTests,properties]

properties :: TestTree
properties = testGroup "Properties" [scProps]

scProps :: TestTree
scProps = testGroup "(checked by SmallCheck)"
  [ testPropDepth 7 "small maps of degree 3, all permutations"
      (over (series :: Series IO [Positive Int]) (ordering 3))
  , testPropDepth 7 "small maps of degree 4, all permutations"
      (over (series :: Series IO [Positive Int]) (ordering 4))
  , testPropDepth 10 "medium maps of degree 3, few permutations"
      (over doubletonSeriesA (ordering 3))
  , testPropDepth 10 "medium maps of degree 4, few permutations"
      (over doubletonSeriesA (ordering 4))
  , testPropDepth 10 "medium maps of degree 3, repeat keys likely, few permutations"
      (over doubletonSeriesB (ordering 3))
  , testPropDepth 10 "medium maps of degree 4, repeat keys likely, few permutations"
      (over doubletonSeriesB (ordering 4))
  , testPropDepth 500 "large maps of degree 3, repeat keys certain, one permutation"
      (over singletonSeriesB (ordering 3))
  , testPropDepth 500 "large maps of degree 6, one permutation"
      (over singletonSeriesA (ordering 6))
  , testPropDepth 500 "large maps of degree 7, repeat keys certain, one permutation"
      (over singletonSeriesB (ordering 7))
  ]

unitTests :: TestTree
unitTests = testGroup "Unit tests"
  [ testCase "put followed by get (tests lookup,insert,toAscList)" $ do
      let xs = [1,3,2,4,6,5 :: Word]
          xs' = map (\x -> (x,x)) xs
          e = runST $ runExceptT $ do
            b <- lift $ B.fromList 20 xs'
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
      actual <- return (runST (B.fromList 4 xs' >>= B.toAscList))
      actual @?= S.toAscList (S.fromList xs')
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
        m <- B.new degree
        forM_ xs $ \x -> do
          B.insert m x x
        (,) <$> B.toAscList m <*> B.debugMap m
  in if actual == expected
    then Right "good"
    else Left $ concat
      [ "expected: "
      , show expected
      , ", actual: "
      , show actual
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

