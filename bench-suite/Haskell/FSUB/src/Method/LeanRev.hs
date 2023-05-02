{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell #-}

module Method.LeanRev where

import Bench.Lib
import Impl
import Spec
import Test.LeanCheck

instance Listable Typ where
  tiers = cons2 All \/ cons2 Arr \/ cons1 TVar \/ cons0 Top

instance Listable Term where
  tiers = cons2 TApp \/ cons2 TAbs \/ cons2 App \/ cons2 Abs \/ cons1 Var

$( mkMethods
     [|lcRun Naive maxCap|]
     [ 'prop_SinglePreserve,
       'prop_MultiPreserve
     ]
 )