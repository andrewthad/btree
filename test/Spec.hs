{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE BangPatterns #-}

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

import qualified Map.Mutable.BTree.Prim as B
import qualified Data.Set as S

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "Tests" [unitTests] -- ,properties]

properties :: TestTree
properties = testGroup "Properties" [scProps]

scProps :: TestTree
scProps = testGroup "(checked by SmallCheck)"
  [ testPropDepth 4 "ordering, small maps, all permutations" (ordering 6)
  , SC.testProperty "Fermat's little theorem" $
      \x -> ((x :: Integer)^7 - x) `mod` 7 == 0
  -- the following property does not hold
  , SC.testProperty "Fermat's last theorem" $
      \x y z n ->
        (n :: Integer) >= 3 SC.==> x^n + y^n /= (z^n :: Integer)
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

ordering :: 
     Int -- ^ degree of b-tree
  -> [Positive Int] -- ^ values to insert
  -> Either Reason Reason
ordering degree xs' = 
  let xs = map getPositive xs'
      expected = map (\x -> (x,x)) $ S.toAscList $ S.fromList xs
      actual = runST $ do
        m <- B.new degree
        forM_ (traceShowId xs) $ \x -> do
          B.insert m x x
        B.toAscList m
  in if actual == expected
    then Right "good"
    else Left $ concat
      [ "expected: "
      , show expected
      , ", actual: "
      , show actual
      ]

