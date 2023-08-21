{-# LANGUAGE ImportQualifiedPost #-}

module Spec where

import Data.Char (isAlphaNum, isLower, isSpace, isUpper)
import Data.List (isInfixOf)
import Etna.Lib
import GHC.Unicode (isPrint)
import Level
import LuParser
import LuSyntax
import Parser (Parser)
import Parser qualified as P
import PrettyPrinter
import Test.QuickCheck qualified as QC

reserved :: [String]
reserved =
  [ "and",
    "break",
    "do",
    "else",
    "elseif",
    "end",
    "false",
    "for",
    "function",
    "goto",
    "if",
    "in",
    "local",
    "nil",
    "not",
    "or",
    "repeat",
    "return",
    "then",
    "true",
    "until",
    "while"
  ]

doesNotContainEscapeChar :: String -> Bool
doesNotContainEscapeChar s = not ("\"" `isInfixOf` s) && foldr (\x acc -> (isPrint x || isSpace x) && acc) True s

doesNotContainReservedWords :: String -> Bool
doesNotContainReservedWords s = not $ foldr (\x acc -> x `isInfixOf` s || acc) False Spec.reserved

containsOnlyAlphaNumeralsOrUnderscore :: String -> Bool
containsOnlyAlphaNumeralsOrUnderscore = foldr (\x acc -> (isAlphaNum x || x == '_') && acc) True

isNotEmpty :: String -> Bool
isNotEmpty s = s /= ""

startWithLowerUpperOrUnderscore :: String -> Bool
startWithLowerUpperOrUnderscore (x : _) = isUpper x || isLower x || x == '_'

nameIsParsable :: VarName -> Bool
nameIsParsable (VarName n) = doesNotContainReservedWords n && isNotEmpty n && startWithLowerUpperOrUnderscore n && containsOnlyAlphaNumeralsOrUnderscore n

blockIsParsable :: Block -> Bool
blockIsParsable (Block ss) = foldr (\s acc -> statementIsParsable s && acc) True ss

statementIsParsable :: Statement -> Bool
statementIsParsable (Assign v e) = varIsParsable v && expressionIsParsable e
statementIsParsable (If e b1 b2) = expressionIsParsable e && blockIsParsable b1 && blockIsParsable b2
statementIsParsable (While e b) = expressionIsParsable e && blockIsParsable b
statementIsParsable (Repeat b e) = blockIsParsable b && expressionIsParsable e
statementIsParsable _ = True

varIsParsable :: Var -> Bool
varIsParsable (Name n) = nameIsParsable n
varIsParsable (Dot e n) = expressionIsParsable e && nameIsParsable n
varIsParsable (Proj e1 e2) = expressionIsParsable e1 && expressionIsParsable e2

expressionIsParsable :: Expression -> Bool
expressionIsParsable (Var v) = varIsParsable v
expressionIsParsable (Op1 _ e) = expressionIsParsable e
expressionIsParsable (Op2 e1 _ e2) = expressionIsParsable e1 && expressionIsParsable e2
expressionIsParsable (TableConst xs) =
  foldr
    ( \x acc -> case x of
        (FieldName n e) -> nameIsParsable n && expressionIsParsable e && acc
        (FieldKey e1 e2) -> expressionIsParsable e1 && expressionIsParsable e2 && acc
    )
    True
    xs
expressionIsParsable (Val v) = valueIsParsable v

valueIsParsable :: Value -> Bool
valueIsParsable (StringVal s) = doesNotContainEscapeChar s
valueIsParsable _ = True

prop_roundtrip_val :: Task Value
prop_roundtrip_val v = valueIsParsable v --> P.parse valueP (pretty v) == Right v

prop_roundtrip_exp :: Task Expression
prop_roundtrip_exp e = expressionIsParsable e --> P.parse expP (pretty e) == Right e

prop_roundtrip_stat :: Task Statement
prop_roundtrip_stat s = statementIsParsable s --> P.parse statementP (pretty s) == Right s