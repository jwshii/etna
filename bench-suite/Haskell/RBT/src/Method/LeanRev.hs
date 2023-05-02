{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell #-}

module Method.LeanRev where

import Bench.Lib
import Impl
import Method.SpecRev
import Spec (Key (..), RBT, Val (..))
import Test.LeanCheck

deriveListable ''Key

deriveListable ''Val

deriveListable ''Color

deriveListable ''Tree

$( mkMethods
     [|lcRun Naive maxCap|]
     [ 'prop_InsertValid,
       'prop_DeleteValid,
       'prop_InsertPost,
       'prop_DeletePost,
       'prop_InsertModel,
       'prop_DeleteModel,
       'prop_InsertInsert,
       'prop_InsertDelete,
       'prop_DeleteInsert,
       'prop_DeleteDelete
     ]
 )