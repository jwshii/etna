{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell #-}

module Method.Lean where

import Bench.Lib
import Impl
import Spec
import Test.LeanCheck

deriveListable ''Typ
deriveListable ''Expr

$( mkMethods
     [|lcRun Naive maxCap|]
     [ 'prop_SinglePreserve,
       'prop_MultiPreserve
     ]
 )