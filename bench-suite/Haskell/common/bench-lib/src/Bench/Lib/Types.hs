{-# LANGUAGE DeriveGeneric #-}

module Bench.Lib.Types where

import Data.Aeson (FromJSON)
import Data.Functor
import GHC.Generics

data Result = Result
  { foundbug :: Bool,
    passed :: Int,
    discards :: Maybe Int,
    output :: String
  }
  deriving (Show)

type Cap = Int

type PropPair = (Bool, Bool) -- (precondition, postcondition)

(-->) :: Bool -> Bool -> PropPair
(-->) = (,)

infixr 0 -->

type Task a = a -> PropPair

type Method a = Task a -> IO Result

data Approach = Correct | Naive

data MArgs = MArgs
  { file :: String,
    trials :: Int,
    bench :: String,
    method :: String,
    mutant :: String,
    property :: String,
    label :: String,
    timeout :: Maybe Double
  }
  deriving (Generic, Show)

instance FromJSON MArgs