{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}

module Strategy.Hybrid where

import Data.Char qualified as Char
import Etna.Lib
import GHC.Generics (Generic)
import Generic.Random
import LuSyntax
import Parser (Parser)
import Parser qualified as P
import Spec
import Test.QuickCheck hiding (Result)
import Test.QuickCheck qualified as QC

deriving instance Generic VarName

instance Arbitrary VarName where
  -- \| Generate a small set of names for generated tests. These names are guaranteed to not include
  -- reserved words. Copied from Correct.hs
  arbitrary = QC.elements $ map VarName ["_", "_G", "x", "X", "y", "x0", "X0", "xy", "XY", "_x"]

-- | Generate a string literal, being careful about the characters that it may contain. Copied from Correct.hs
genStringLit :: Gen String
genStringLit = escape <$> QC.listOf (QC.elements stringLitChars)
  where
    escape :: String -> String
    escape = foldr Char.showLitChar ""
    stringLitChars :: [Char]
    stringLitChars = filter (\c -> c /= '\"' && (Char.isSpace c || Char.isPrint c)) ['\NUL' .. '~']

deriving instance Generic Var

instance Arbitrary Var where
  arbitrary = genericArbitraryRec uniform `withBaseCase` (Name <$> arbitrary)

deriving instance Generic Expression

instance Arbitrary Expression where
  arbitrary = genericArbitraryRec uniform `withBaseCase` (Val <$> arbitrary)

-- Copied from Correct.hs
genTableFields :: Int -> Gen [TableField]
genTableFields n = do
  len <- QC.elements [0 .. 3]
  take len <$> QC.infiniteListOf (genTableField n)

genTableField :: Int -> Gen TableField
genTableField n =
  QC.oneof
    [ FieldName <$> arbitrary <*> arbitrary,
      FieldKey <$> arbitrary <*> arbitrary
    ]
  where
    n' = n `div` 2

deriving instance Generic TableField

instance Arbitrary TableField where
  arbitrary = QC.sized genTableField

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
  arbitrary =
    QC.oneof
      [ IntVal <$> arbitrary,
        BoolVal <$> arbitrary,
        pure NilVal,
        StringVal <$> genStringLit
        -- note: do not generate table values
      ]

$( mkStrategies
     [|qcRunArb qcDefaults Correct|]
     [ 'prop_roundtrip_val,
       'prop_roundtrip_exp,
       'prop_roundtrip_stat
     ]
 )
