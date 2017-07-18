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
import Control.Monad.Trans.Class
import Data.Word
import Data.Int
import Data.Proxy
import Data.Primitive.Types
import Data.Foldable
import Data.Primitive.Compact (withToken,getSizeOfCompact)
import System.IO.Unsafe
import Data.Hashable
import Foreign.Storable (Storable)

import qualified Data.List as L
import qualified Data.List.NonEmpty as NE
import qualified BTree as B
import qualified BTree.Linear as BTL
import qualified BTree.Store as BTS
import qualified Data.Set as S
import qualified Data.Primitive.PrimArray as P

main :: IO ()
main = do
  putStrLn "Starting test suite"
  -- BTS.with $ \bt0 -> do
  --   bt1 <- BTS.insert bt0 (4 :: Int) 'x'
  --   bt2 <- BTS.insert bt1 3 'z'
  --   BTS.toAscList bt2 >>= print 
  defaultMain tests
  -- basicBenchmarks
  putStrLn "Finished test suite"

tests :: TestTree
tests = testGroup "Tests" [unitTests,properties]

properties :: TestTree
properties = testGroup "Properties" [scProps]

smallcheckTests :: 
     (forall n. (Storable n, Show n, Ord n, Prim n, Hashable n, Bounded n, Integral n) => Int -> [Positive n] -> Either Reason Reason)
  -> [TestTree]
smallcheckTests f = 
  [ testPropDepth 3 "small maps of degree 3, all permutations, no splitting"
      (over (series :: Series IO [Positive Int]) (f 3))
  , testPropDepth 4 "small maps of degree 3, all permutations, one split"
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
  , testPropDepth 150 "large maps of degree 3, repeat keys certain, one permutation"
      (over singletonSeriesB (f 3))
  , testPropDepth 150 "large maps of degree 6, one permutation"
      (over singletonSeriesA (f 6))
  , testPropDepth 150 "large maps of degree 7, repeat keys certain, one permutation"
      (over singletonSeriesB (f 7))
  ]

scProps :: TestTree
scProps = testGroup "smallcheck"
  [ testGroup "standard heap" (smallcheckTests ordering) 
  , testGroup "unmanaged heap" (smallcheckTests orderingStorable)
  , testPropDepth 7 "standard heap lookup"
      (over (series :: Series IO [Positive Int]) (lookupAfterInsert 3))
  , testPropDepth 500 "standard heap bigger lookup"
      (over singletonSeriesA (lookupAfterInsert 3))
  , testPropDepth 7 "compact heap lookup"
      (over (series :: Series IO [Positive Int]) (lookupAfterInsertCompact 3))
  , testPropDepth 500 "compact heap bigger lookup"
      (over singletonSeriesA (lookupAfterInsertCompact 10))
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
  , testCase "unmanaged b-tree can be created" $ BTS.with $ \_ -> do
      return ()
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

lookupAfterInsertUnmanaged :: (Show n, Ord n, Prim n)
  => Int -- ^ degree of b-tree
  -> [Positive n] -- ^ values to insert
  -> Either Reason Reason
lookupAfterInsertUnmanaged degree xs' =
  let xs = map getPositive xs'
      expected = map (\x -> (x,x)) $ S.toAscList $ S.fromList xs
   in fmap (const "good") $ unsafePerformIO $ BTS.with $ \m0 -> do
        m1 <- foldlM (\ !m !x -> BTS.insert c m x x) m0 xs
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
        return (r1 >> r2)


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

orderingCompact :: (Show n, Ord n, Prim n)
  => Int -- ^ degree of b-tree
  -> [Positive n] -- ^ values to insert
  -> Either Reason Reason
orderingCompact degree xs' = 
  let xs = map getPositive xs'
      expected = map (\x -> (x,x)) $ S.toAscList $ S.fromList xs
      (actual,layout) = runST $ withToken $ \c -> do
        m0 <- BTC.new c degree
        m1 <- foldlM (\ !m !x -> BTC.insert c m x x) m0 xs
        (,) <$> BTC.toAscList m1 <*> BTC.debugMap m1
  in if actual == expected
    then Right "good"
    else Left (notice (show expected) (show actual) layout)

orderingStorable :: (Show n, Ord n, Storable n)
  => Int -- ^ degree of b-tree, ignored
  -> [Positive n] -- ^ values to insert
  -> Either Reason Reason
orderingStorable degree xs' = 
  let xs = map getPositive xs'
      expected = map (\x -> (x,x)) $ S.toAscList $ S.fromList xs
      result = unsafePerformIO $ BTS.with $ \m0 -> do
        m1 <- foldlM (\ !m !x -> BTS.insert m x x) m0 xs
        actual <- BTS.toAscList m1
        return $ if actual == expected
          then Right "good"
          else Left (notice (show expected) (show actual) "layout not available")
   in result

-- let us begin the most dangerous game.
orderingNested :: (Show n, Ord n, Prim n, Hashable n, Bounded n, Integral n)
  => Int -- ^ degree of b-tree
  -> [Positive n] -- ^ values to insert
  -> Either Reason Reason
orderingNested degree xs' = 
  let xs = map getPositive xs'
      e = runST $ withToken $ \c -> do
        m0 <- BTT.new c degree
        m1 <- foldlM
          (\ !mtop !x -> do
            let subValues = take 10 (iterate (fromIntegral . hashWithSalt 13 . (+ div maxBound 3)) x)
            foldM ( \ !m !y -> do
                ((),t) <- BTT.modifyWithM c m x (BTC.new c degree) $ \mbottom -> do
                  bt <- BTC.insert c mbottom y y
                  return (BTT.Replace () bt)
                return t
              ) mtop subValues
          ) m0 xs
        runExceptT $ forM_ xs $ \x -> do
          m <- lift $ BTT.lookup m1 x 
          case m of
            Nothing -> ExceptT (return (Left ("could not find " ++ show x ++ " in top b-tree")))
            Just b -> do
              n <- lift $ BTC.lookup b x
              case n of
                Nothing -> ExceptT (return (Left ("could not find " ++ show x ++ " in bottom b-tree")))
                Just k -> return ()
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

doubletonSeriesA :: Series m [Positive Word16]
doubletonSeriesA = (fmap.fmap) Positive (scanSeries (\n -> [n + 9787, n + 29059]) 0)

doubletonSeriesB :: Series m [Positive Word8]
doubletonSeriesB = (fmap.fmap) Positive (scanSeries (\n -> [n + 89, n + 71]) 0)

singletonSeriesA :: Series m [Positive Word16]
singletonSeriesA = (fmap.fmap) Positive (scanSeries (\n -> [n + 26399]) 0)

singletonSeriesB :: Series m [Positive Word8]
singletonSeriesB = (fmap.fmap) Positive (scanSeries (\n -> [n + 73]) 0)

 

