{-# LANGUAGE TemplateHaskell #-}

module Main where

import Bench.Lib
import Data.List (lookup)
import Data.Maybe
import Method.Correct as Correct
import Method.Lean as Lean
import Method.LeanRev as LeanRev
import Method.Quick as Quick
import Method.Size as Size
import Method.Small as Small
import Method.SmallRev as SmallRev
import System.Environment (getArgs)

$( mkMain
     ( return
         [ "Correct",
           "Lean",
           "LeanRev",
           "Quick",
           "Size",
           "Small",
           "SmallRev"
         ]
     )
     (allProps "src/Spec.hs")
 )