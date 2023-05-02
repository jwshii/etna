{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TemplateHaskell #-}

module Method.LeanRev where

import Bench.Lib
import Impl
import Method.SpecRev
import Spec (Key (..), Val (..))
import Test.LeanCheck

deriveListable ''Key

deriveListable ''Val

deriveListable ''Tree

$( mkMethods
     [|lcRun Naive maxCap|]
     [ 'prop_InsertValid,
       'prop_DeleteValid,
       'prop_UnionValid,
       'prop_InsertPost,
       'prop_DeletePost,
       'prop_UnionPost,
       'prop_InsertModel,
       'prop_DeleteModel,
       'prop_UnionModel,
       'prop_InsertInsert,
       'prop_InsertDelete,
       'prop_InsertUnion,
       'prop_DeleteInsert,
       'prop_DeleteDelete,
       'prop_DeleteUnion,
       'prop_UnionDeleteInsert,
       'prop_UnionUnionIdem,
       'prop_UnionUnionAssoc
     ]
 )