{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

module Etna.Lib.Strategy.Hedgehog (hedgeRun, hedgeDefaults) where

import Etna.Lib.Types hiding (property)
import Etna.Lib.Util
import Control.Monad
import Data.List (isInfixOf)
import Hedgehog
import Hedgehog.Gen
import Hedgehog.Internal.Config
import Hedgehog.Internal.Runner
import Hedgehog.Range
import System.IO.Silently
import Text.Regex.PCRE

type Args = (TestLimit, DiscardLimit)

hedgeDefaults :: Args
hedgeDefaults = (toEnum maxCap, toEnum maxCap)

makeProp :: Show a => Gen a -> Approach -> Task a -> Property
makeProp gen Naive task = property $ do
  a <- forAll gen
  let (pre, post) = task a
  guard pre
  assert post
makeProp gen Correct task = property $ do
  a <- forAll gen
  assert (snd $ task a)

hedgeRun :: Show a => Gen a -> Approach -> Args -> Strategy a
hedgeRun gen app (tests, discards) task = do
  (out, result) <- capture $ check prop
  let foundbug = not result
      passed = numTests out - if foundbug then 1 else 0
      discards = Just $ numDiscards out
      output = ""
  return Result {..}
  where
    prop =
      withShrinks 0 $
        withTests tests $
          withDiscards discards $
            makeProp gen app task

    numTests :: String -> Int
    numTests out = read $ extractGroup out "([\\d]+) test"

    numDiscards :: String -> Int
    numDiscards out
      | "discard" `isInfixOf` out = read $ extractGroup out "([\\d]+) discard"
      | otherwise = 0

    extractGroup :: String -> String -> String
    extractGroup out regex =
      let matches = show out =~ regex :: [[String]]
       in head matches !! 1