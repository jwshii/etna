module Level where

import LuSyntax

level :: Bop -> Int
{-! -}
level Times = 7
level Divide = 7
level Plus = 5
level Minus = 5
{-!! level_1 -}
{-!
level Times = 5
level Divide = 5
level Plus = 7
level Minus = 7
-}
level Concat = 4
level _ = 3 -- comparison operators