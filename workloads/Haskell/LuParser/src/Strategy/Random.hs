{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}

module Strategy.Random where

import Data.Char qualified as Char
import Etna.Lib
  ( Approach (Correct, Naive),
    mkStrategies,
    qcDefaults,
    qcRunArb,
  )
import GHC.Generics (Generic)
import Generic.Random
import LuParser (valueP)
import LuSyntax
import Parser (Parser)
import Parser qualified as P
import PrettyPrinter (pretty)
import Spec
import Test.QuickCheck hiding (Result)
import Test.QuickCheck qualified as QC

deriving instance Generic VarName

instance Arbitrary VarName where
  arbitrary = VarName <$> arbitrary

deriving instance Generic Var

instance Arbitrary Var where
  arbitrary = genericArbitraryRec uniform `withBaseCase` (Name <$> arbitrary)

deriving instance Generic Expression

instance Arbitrary Expression where
  arbitrary = genericArbitraryRec uniform `withBaseCase` (Val <$> arbitrary)

deriving instance Generic TableField

instance Arbitrary TableField where
  arbitrary = genericArbitraryRec uniform

deriving instance Generic Statement

instance Arbitrary Statement where
  arbitrary = genericArbitraryRec uniform `withBaseCase` QC.oneof [Assign <$> arbitrary <*> arbitrary, return Empty]

deriving instance Generic Block

instance Arbitrary Block where
  arbitrary = genericArbitraryRec uniform `withBaseCase` pure mempty

deriving instance Generic Uop

instance Arbitrary Uop where
  arbitrary = QC.arbitraryBoundedEnum

deriving instance Generic Bop

instance Arbitrary Bop where
  arbitrary = QC.arbitraryBoundedEnum

deriving instance Generic Value

instance Arbitrary Value where
  arbitrary = genericArbitraryRec uniform

$( mkStrategies
     [|qcRunArb qcDefaults Naive|]
     [ 'prop_roundtrip_val,
       'prop_roundtrip_exp,
       'prop_roundtrip_stat
     ]
 )