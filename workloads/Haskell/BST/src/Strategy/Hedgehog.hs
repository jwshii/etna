module Strategy.Hedgehog where

import Control.Monad
import Etna.Lib
import Hedgehog
import Hedgehog.Gen
import Hedgehog.Range
import Impl
import Spec

genKey :: Gen Key
genKey = Key <$> int (linear 0 10)

genVal :: Gen Val
genVal = Val <$> bool

genBST :: Gen BST
genBST =
  recursive
    choice
    [pure E]
    [T <$> genBST <*> genKey <*> genVal <*> genBST]

test_InsertPost = hedgeRun gen Naive hedgeDefaults prop_InsertPost
  where
    gen = liftM4 (,,,) genBST genKey genKey genVal