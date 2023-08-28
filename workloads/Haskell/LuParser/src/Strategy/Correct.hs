{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE TemplateHaskell #-}

module Strategy.Correct where

import Data.Char qualified as Char
import Etna.Lib
import LuSyntax
import Parser qualified as P
import Spec
import Test.QuickCheck hiding (Result)
import Test.QuickCheck qualified as QC

-- | Generate a small set of names for generated tests. These names are guaranteed to not include
-- reserved words
genName :: Gen VarName
genName = QC.elements $ map VarName ["_", "_G", "x", "X", "y", "x0", "X0", "xy", "XY", "_x"]

-- | Generate a string literal, being careful about the characters that it may contain
genStringLit :: Gen String
genStringLit = escape <$> QC.listOf (QC.elements stringLitChars)
  where
    -- escape special characters appearing in the string,
    escape :: String -> String
    escape = foldr Char.showLitChar ""
    -- generate strings containing printable characters or spaces, but not including '\"'
    stringLitChars :: [Char]
    stringLitChars = filter (\c -> c /= '\"' && (Char.isSpace c || Char.isPrint c)) ['\NUL' .. '~']

-- | Generate a size-controlled global variable or table field
genVar :: Int -> Gen Var
genVar 0 = Name <$> genName
genVar n =
  QC.frequency
    [ (1, Name <$> genName),
      (n, Dot <$> genExp n' <*> genName),
      (n, Proj <$> genExp n' <*> genExp n')
    ]
  where
    n' = n `div` 2

-- | Generate a size-controlled expression
genExp :: Int -> Gen Expression
genExp 0 = QC.oneof [Var <$> genVar 0, Val <$> arbitrary]
genExp n =
  QC.frequency
    [ (1, Var <$> genVar n),
      (1, Val <$> arbitrary),
      (n, Op1 <$> arbitrary <*> genExp n'),
      (n, Op2 <$> genExp n' <*> arbitrary <*> genExp n'),
      (n', TableConst <$> genTableFields n')
    ]
  where
    n' = n `div` 2

-- | Generate a list of fields in a table constructor epression.
-- We limit the size of the table to avoid size blow up.
genTableFields :: Int -> Gen [TableField]
genTableFields n = do
  len <- QC.elements [0 .. 3]
  take len <$> QC.infiniteListOf (genTableField n)

genTableField :: Int -> Gen TableField
genTableField n =
  QC.oneof
    [ FieldName <$> genName <*> genExp n',
      FieldKey <$> genExp n' <*> genExp n'
    ]
  where
    n' = n `div` 2

-- | Generate a size-controlled statement
genStatement :: Int -> Gen Statement
genStatement n | n <= 1 = QC.oneof [Assign <$> genVar 0 <*> genExp 0, return Empty]
genStatement n =
  QC.frequency
    [ (1, Assign <$> genVar n' <*> genExp n'),
      (1, return Empty),
      (n, If <$> genExp n' <*> genBlock n' <*> genBlock n'),
      -- generate loops half as frequently as if statements
      (n', While <$> genExp n' <*> genBlock n'),
      (n', Repeat <$> genBlock n' <*> genExp n')
    ]
  where
    n' = n `div` 2

genBlock :: Int -> Gen Block
genBlock n = Block <$> genStmts n
  where
    genStmts 0 = pure []
    genStmts n =
      QC.frequency
        [ (1, return []),
          (n, (:) <$> genStatement n' <*> genStmts n')
        ]
      where
        n' = n `div` 2

instance Arbitrary Var where
  arbitrary = QC.sized genVar

instance Arbitrary Statement where
  arbitrary = QC.sized genStatement

instance Arbitrary TableField where
  arbitrary = QC.sized genTableField

instance Arbitrary Block where
  arbitrary = QC.sized genBlock

instance Arbitrary Expression where
  arbitrary = QC.sized genExp

instance Arbitrary Uop where
  arbitrary = QC.arbitraryBoundedEnum

instance Arbitrary Bop where
  arbitrary = QC.arbitraryBoundedEnum

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
