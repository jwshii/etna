{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE RecordWildCards #-}

module Bench.Lib.Trial (benchMany) where

import Bench.Lib.Types (Result (Result))
import qualified Bench.Lib.Types as B
import Control.Monad (forM)
import Data.Aeson (ToJSON, encode)
import Data.ByteString.Lazy.Char8 as B8 (appendFile)
import Data.Char (toLower)
import Data.IORef (modifyIORef, newIORef, readIORef)
import Data.List (intercalate)
import Data.Maybe (fromMaybe)
import GHC.Generics (Generic)
import System.Clock (Clock (..), getTime, toNanoSecs)
import System.IO.Silently (silence)
import System.TimeIt (timeItT)
import System.Timeout (timeout)
import Text.Printf (printf)

data BenchResult = BenchResult
  { bench :: String,
    method :: String,
    mutant :: String,
    property :: String,
    foundbug :: Bool,
    passed :: Maybe Int,
    discards :: Maybe Int,
    time :: Double,
    output :: String
  }
  deriving (Generic)

instance ToJSON BenchResult

type Trials = Int

type Timeout = Maybe Double

type Info = (String, String, String, String)

-- TODO: negative?
benchOne :: Info -> Timeout -> IO Result -> IO BenchResult
benchOne (bench, method, mutant, property) mtimeout test = do
  case mtimeout of
    Nothing -> run
    Just t -> fromMaybe (defaultResult t) <$> timeout (fromSec t) run
  where
    run = do
      (time, Result {..}) <- myTimeIt $ eval $ silence test
      return BenchResult {passed = Just passed, ..}

    fromSec :: Double -> Int
    fromSec = round . (1000000 *)

    -- TODO: indicate timeout more cleanly
    defaultResult time =
      BenchResult
        { foundbug = False,
          passed = Nothing,
          discards = Nothing,
          output = "",
          ..
        }

-- Based on `System.TimeIt`
myTimeIt :: IO a -> IO (Double, a)
myTimeIt ioa = do
  mt1 <- getTime Monotonic
  a <- ioa
  mt2 <- getTime Monotonic
  let t t2 t1 = fromIntegral (toNanoSecs t2 - toNanoSecs t1) * 1e-9
  return (t mt2 mt1, a)

-- TODO: use deepseq to do this instead?
eval :: IO Result -> IO Result
eval ia = do
  Result {..} <- ia
  return Result {..}
{-# NOINLINE eval #-}

benchMany :: FilePath -> Trials -> Info -> Timeout -> IO Result -> IO ()
benchMany file _ info timeout test = do
  -- TODO: fix the names here
  result <- benchOne info timeout test
  B8.appendFile file (encode result)
  Prelude.appendFile file "\n"