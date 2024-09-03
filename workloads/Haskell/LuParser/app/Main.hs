{-# LANGUAGE TemplateHaskell #-}

module Main where

import Control.Monad (liftM2)
import Data.List (lookup)
import Data.Maybe
import Etna.Lib
import Strategy.Correct as Correct
import Strategy.Hybrid as Hybrid
import Strategy.Random as Random
import System.Environment (getArgs)

$( mkMain
     ( return
         [ "Correct",
           "Hybrid",
           "Random"
         ]
     )
     (allProps "src/Spec.hs")
 )