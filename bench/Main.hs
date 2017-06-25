{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE TypeFamilies #-}

{-# OPTIONS_GHC -O2 #-}

module Main
  ( main
  ) where

import qualified BTree.Linear as BTL
import qualified BTree.Compact as BTC
import Control.Monad
import Data.Primitive.Compact (Token,withToken)
import GHC.Prim
import System.Mem (performGC)
import Data.Hashable
import Data.Maybe
import System.Clock

-- this specialization does not seem to work.
{-# SPECIALIZE BTC.modifyWithM :: BTC.Context RealWorld c -> BTC.BTree RealWorld Int Int c -> Int -> (Maybe Int -> IO Int) -> IO (Int, BTC.BTree RealWorld Int Int c) #-}

main :: IO ()
main = do
  putStrLn "Starting benchmark suite"
  let multiplier = 5
  let total   = 200000 * multiplier
      range   = 10000000 * multiplier
      lookups = 100000 * multiplier
  putStrLn $ concat
    [ "This benchmark will insert "
    , show total
    , " numbers into a b-tree. The range of these "
    , " numbers is from 0 to "
    , show (range - 1)
    , ". Then, we try looking up the numbers from "
    , "0 to "
    , show (lookups - 1)
    ]
  replicateM_ 1 $ do
    buildStart <- getTime Monotonic
    (b,ctx) <- onHeapBTree total range
    buildEnd <- getTime Monotonic
    performGC
    start <- getTime Monotonic
    x <- lookupMany lookups b ctx
    end <- getTime Monotonic
    putStrLn ("Accumulated sum (not a benchmark): " ++ show x)
    putStrLn "On-heap tree, Amount of time taken to build: "
    putStrLn (showTimeSpec (diffTimeSpec buildEnd buildStart))
    putStrLn "On-heap tree, Amount of time taken for lookups: "
    putStrLn (showTimeSpec (diffTimeSpec end start))
    performGC
  withToken $ \token -> do
    buildStart <- getTime Monotonic
    (b,ctx) <- offHeapBTree token total range
    buildEnd <- getTime Monotonic
    performGC
    start <- getTime Monotonic
    x <- lookupManyOffHeap lookups b
    end <- getTime Monotonic
    putStrLn ("Accumulated sum (not a benchmark): " ++ show x)
    putStrLn "Off-heap tree, Amount of time taken to build: "
    putStrLn (showTimeSpec (diffTimeSpec buildEnd buildStart))
    putStrLn "Off-heap tree, Amount of time taken for lookups: "
    putStrLn (showTimeSpec (diffTimeSpec end start))
  
lookupMany :: Int -> BTL.BTree RealWorld Int Int -> BTL.Context RealWorld -> IO Int
lookupMany total b ctx = go 0 0
  where
  go !n !s = if n < total
    then do
      m <- BTL.lookup ctx b n
      go (n + 1) (s + fromMaybe 0 m)  
    else return s

lookupManyOffHeap :: Int -> BTC.BTree RealWorld Int Int c -> IO Int
lookupManyOffHeap total b = go 0 0
  where
  go !n !s = if n < total
    then do
      m <- BTC.lookup b n
      go (n + 1) (s + fromMaybe 0 m) 
    else return s
  
onHeapBTree :: Int -> Int
  -> IO (BTL.BTree RealWorld Int Int, BTL.Context RealWorld)
onHeapBTree total range = do
  let ctx = BTL.Context 100
  b0 <- BTL.new ctx
  let go !n !b = if n < total
        then do
          let x = mod (hashWithSalt mySalt n) range
          b' <- BTL.insert ctx b x x
          go (n + 1) b'
        else return (b,ctx)
  go 0 b0

offHeapBTree ::
     Token c 
  -> Int
  -> Int
  -> IO (BTC.BTree RealWorld Int Int c, BTC.Context RealWorld c)
offHeapBTree token total range = do
  ctx <- BTC.newContext 100 token
  b0 <- BTC.new ctx
  let go !n !b = if n < total
        then do
          let x = mod (hashWithSalt mySalt n) range
          b' <- BTC.insert ctx b x x
          go (n + 1) b'
        else return (b,ctx)
  go 0 b0


mySalt :: Int
mySalt = 2343

showTimeSpec :: TimeSpec -> String
showTimeSpec (TimeSpec s ns) = 
  show (fromIntegral s + (fromIntegral ns / 1000000000) :: Double)
