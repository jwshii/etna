{-# LANGUAGE TemplateHaskell #-}

module Main where

import Bench.Lib
import Data.List (lookup)
import Data.Maybe
import Method.Correct as Correct
import Method.Lean as Lean
import Method.LeanRev as LeanRev
import Method.Quick as Quick
import Method.Small as Small
import Method.SmallRev as SmallRev
import System.Environment (getArgs)

$( mkMain
     ( return
         [ "Correct",
           "Lean",
           "LeanRev",
           "Quick",
           "Small",
           "SmallRev"
         ]
     )
     (allProps "src/Spec.hs")
 )