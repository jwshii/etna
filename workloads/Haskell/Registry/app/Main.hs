{-# LANGUAGE TemplateHaskell #-}

module Main where

import Data.List (lookup)
import Data.Maybe
import Etna.Lib
import Strategy.Correct as Correct
import System.Environment (getArgs)

$( mkMain
     ( return
         [ "Correct"
         ]
     )
     (allProps "src/Spec.hs")
 )