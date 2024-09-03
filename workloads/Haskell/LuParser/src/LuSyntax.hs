module LuSyntax where

import Control.Applicative

-- Code in this file is adapted from a CIS 5520 homework assignment at Penn.

newtype Block = Block [Statement] -- s1 ... sn
  deriving (Eq, Show)

instance Semigroup Block where
  Block s1 <> Block s2 = Block (s1 <> s2)

instance Monoid Block where
  mempty = Block []

data Statement
  = Assign Var Expression -- x = e
  | If Expression Block Block -- if e then s1 else s2 end
  | While Expression Block -- while e do s end
  | Empty -- ';'
  | Repeat Block Expression -- repeat s until e
  deriving (Eq, Show)

data Expression
  = Var Var -- global variables x and table indexing
  | Val Value -- literal values
  | Op1 Uop Expression -- unary operators
  | Op2 Expression Bop Expression -- binary operators
  | TableConst [TableField] -- table construction, { x = 3 , y = 5 }
  deriving (Eq, Show)

data Value
  = NilVal -- nil
  | IntVal Int -- 1
  | BoolVal Bool -- false, true
  | StringVal String -- "abd"
  -- table values are ignored
  deriving
    ( Eq,
      Show,
      Ord
    )

data Uop
  = Neg -- `-` :: Int -> Int
  | Not -- `not` :: a -> Bool
  | Len -- `#` :: String -> Int / Table -> Int
  deriving (Eq, Show, Enum, Bounded)

data Bop
  = Plus -- `+`  :: Int -> Int -> Int
  | Minus -- `-`  :: Int -> Int -> Int
  | Times -- `*`  :: Int -> Int -> Int
  | Divide -- `//` :: Int -> Int -> Int   -- floor division
  | Modulo -- `%`  :: Int -> Int -> Int   -- modulo
  | Eq -- `==` :: a -> a -> Bool
  | Gt -- `>`  :: a -> a -> Bool
  | Ge -- `>=` :: a -> a -> Bool
  | Lt -- `<`  :: a -> a -> Bool
  | Le -- `<=` :: a -> a -> Bool
  | Concat -- `..` :: String -> String -> String
  deriving (Eq, Show, Enum, Bounded)

newtype VarName = VarName String deriving (Eq, Show) -- either the name of a variable or the name of a field

data Var
  = Name VarName -- x, global variable
  | Dot Expression VarName -- t.x, access table using string key
  | Proj Expression Expression -- t[1], access table table using any type of key
  deriving (Eq, Show)

data TableField
  = FieldName VarName Expression -- x = 3,
  | FieldKey Expression Expression -- ["x"] = true , [1] = 4 , [true] = "a"
  deriving (Eq, Show)