module IR where

import AST

-- https://en.wikipedia.org/wiki/B%2C_C%2C_K%2C_W_system
data IR
  = B IR IR IR
  | C IR IR IR
  | K IR IR
  | W IR IR

fromAST :: Expr -> IR
fromAST = undefined

interpret :: IR -> IR
interpret = undefined
