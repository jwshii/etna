{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# HLINT ignore "Use infix" #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module LuParser where

import Control.Applicative
import Data.Char (isAlpha)
import Data.Char qualified as Char
import LuSyntax
import Parser (Parser)
import Parser qualified as P
import GHC.Base (eqChar)
import Level

-- Code in this file is adapted from a CIS 5520 homework assignment at Penn.

-- Parser implementation
wsP :: Parser a -> Parser a
wsP p = p <* spaces
  where
    spaces :: Parser String
    {-! -}
    spaces = (:) <$> P.space <*> spaces <|> pure []
    {-!! wsP_1 -}
    {-!
    spaces = (:) <$> P.space <*> (spaces <|> pure [])
    -}

stringP :: String -> Parser ()
{-! -}
stringP s = () <$ wsP (P.string s)
{-!! stringP_1 -}
{-!
stringP s = () <$ P.string s
-}

constP :: String -> a -> Parser a
constP s v = v <$ stringP s

parens :: Parser a -> Parser a
parens x = P.between (stringP "(") x (stringP ")")

braces :: Parser a -> Parser a
braces x = P.between (stringP "{") x (stringP "}")

brackets :: Parser a -> Parser a
brackets x = P.between (stringP "[") x (stringP "]")

valueP :: Parser Value
valueP = intValP <|> boolValP <|> nilValP <|> stringValP

intValP :: Parser Value
intValP = IntVal <$> wsP P.int

boolValP :: Parser Value
{-! -}
boolValP = (\s -> BoolVal True) <$> wsP (P.string "true") <|> (\s -> BoolVal False) <$> wsP (P.string "false")
{-!! boolValP_1 -}
{-!
boolValP = (\s -> BoolVal True) <$> (P.string "true") <|> (\s -> BoolVal False) <$> (P.string "false")
-}

nilValP :: Parser Value
nilValP = NilVal <$ wsP (P.string "nil")

stringValP :: Parser Value
{-! -}
stringValP = StringVal <$> quotes (some any <|> pure [])
{-!! stringValP_1 -}
{-!
stringValP = StringVal <$> quotes (some any)
-}
{-!! stringValP_2 -}
{-!
stringValP = StringVal <$> quotes (some P.alpha)
-}
{-!! stringValP_3 -}
{-!
stringValP = StringVal <$> (quotes (some any) <|> pure [])
-}
  where
    quotes :: Parser a -> Parser a
    quotes x = P.between (P.string "\"") x (stringP "\"")
    any :: Parser Char
    any =
    {-! -}
      P.satisfy $ not . eqChar '\"'
    {-!! stringValP_4 -}
    {-!
      P.satisfy (const True)
    -}

expP :: Parser Expression
expP = compP
  where
    compP = catP `P.chainl1` opAtLevel (level Gt)
    catP = sumP `P.chainl1` opAtLevel (level Concat)
    sumP = prodP `P.chainl1` opAtLevel (level Plus)
    prodP = uopexpP `P.chainl1` opAtLevel (level Times)
    uopexpP =
      baseP
        <|> Op1 <$> uopP <*> uopexpP
    baseP =
      tableConstP
        <|> Var <$> varP
        <|> parens expP
        <|> Val <$> valueP

opAtLevel :: Int -> Parser (Expression -> Expression -> Expression)
opAtLevel l = flip Op2 <$> P.filter (\x -> level x == l) bopP

varP :: Parser Var
varP = mkVar <$> prefixP <*> some indexP <|> (Name . VarName <$> nameP)
  where
    mkVar :: Expression -> [Expression -> Var] -> Var
    mkVar e l = foldr1 (\f p u -> p (Var (f u))) l e

    prefixP :: Parser Expression
    prefixP = parens expP <|> (Var . Name . VarName <$> nameP)

    indexP :: Parser (Expression -> Var)
    indexP =
      flip Dot <$> (P.string "." *> (VarName <$> nameP))
        <|> flip Proj <$> brackets expP


reserved :: [String]
{-! -}
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
{-!! reserved_1 -}
{-!
-- deleted else if
reserved =
  [ "and",
    "break",
    "do",
    "else",
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
-}
{-!! reserved_2 -}
{-!
-- deleted true/false and boolean operators
reserved =
  [ "break",
    "do",
    "else",
    "elseif",
    "end",
    "for",
    "function",
    "goto",
    "if",
    "in",
    "local",
    "nil",
    "repeat",
    "return",
    "then",
    "until",
    "while"
  ]
-}
{-!! reserved_3 -}
{-!
-- deleted loop-related keywords
reserved =
  [ "and",
    "else",
    "elseif",
    "false",
    "function",
    "goto",
    "if",
    "in",
    "local",
    "nil",
    "not",
    "or",
    "return",
    "then",
    "true",
  ]
-}


nameP :: Parser String
{-! -}
nameP = wsP (P.filter (`notElem` reserved) ((:) <$> (P.lower <|> P.upper <|> P.char '_') <*> rest))
{-!! nameP_1 -}
{-!
nameP = wsP ((:) <$> (P.lower <|> P.upper <|> P.char '_') <*> rest)
-}
  where
    rest :: Parser String
    {-! -}
    rest = (:) <$> P.choice [P.alpha, P.char '_', P.digit] <*> rest <|> pure []
    {-!! nameP_2 -}
    {-!
    rest = (:) <$> P.choice [P.alpha, P.char '_'] <*> rest <|> pure []
    -}

uopP :: Parser Uop
uopP = wsP (constP "-" Neg <|> constP "not" Not <|> constP "#" Len)

bopP :: Parser Bop
bopP =
  wsP
    ( constP "+" Plus
        <|> constP "-" Minus
        <|> constP "*" Times
        <|> constP "//" Divide
        <|> constP "%" Modulo
        <|> constP "==" Eq
        {-! -}
        <|> constP ">=" Ge
        <|> constP ">" Gt
        {-!! bofP_1 -}
        {-!
        <|> constP ">" Gt
        <|> constP ">=" Ge
        -}
        <|> constP "<=" Le
        <|> constP "<" Lt
        <|> constP ".." Concat
    )

tableConstP :: Parser Expression
tableConstP = TableConst <$> braces (P.sepBy tableFieldP (wsP (P.char ',')))
  where
    tableFieldP :: Parser TableField
    {-! -}
    tableFieldP = FieldName <$> (VarName <$> nameP) <* wsP (P.char '=') <*> expP <|> FieldKey <$> brackets expP <* wsP (P.char '=') <*> expP
    {-!! tableConstP_1 -}
    {-!
    tableFieldP = FieldName <$> nameP <* wsP (P.char '=') <*> expP <|> FieldKey <$> expP <* wsP (P.char '=') <*> expP
    -}

statementP :: Parser Statement
statementP =
  wsP $
    Assign <$> varP <* wsP (P.char '=') <*> expP
      {-! -}
      <|> If <$> (wsP (stringP "if") *> expP) <* wsP (stringP "then") <*> blockP <* wsP (stringP "else") <*> blockP <* wsP (stringP "end")
      {-!! statementP_1 -}
      {-! 
      <|> If <$> (wsP (stringP "if") *> expP) <* wsP (stringP "then") <*> blockP <* wsP (stringP "else") <*> blockP
      -}
      <|> While <$> (wsP (stringP "while") *> expP) <* wsP (stringP "do") <*> blockP <* wsP (stringP "end")
      <|> wsP (constP ";" Empty)
      <|> Repeat <$> (wsP (stringP "repeat") *> blockP) <* wsP (stringP "until") <*> expP

blockP :: Parser Block
blockP = wsP (Block <$> statementsP)
  where
    statementsP :: Parser [Statement]
    statementsP = (:) <$> statementP <*> (statementsP <|> pure []) <|> pure []

