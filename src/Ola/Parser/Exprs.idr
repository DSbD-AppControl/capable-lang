|||
|||
||| Module    : Exprs.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
module Ola.Parser.Exprs

import Decidable.Equality

import Data.List1

import Ola.Lexer
import Ola.Parser.API

import Ola.Core
import Ola.Types

import Ola.Raw.Types
import Ola.Raw.Exprs

import Ola.Parser.Types

%default partial -- @TODO Make exprs parsing total.


export
var : Rule Expr
var
  = pure (Var !Ola.ref)

constants : Rule Expr
constants
    = unit <|> char <|> string <|> int <|> bool
  where
    unit : Rule Expr
    unit
      = do s <- Toolkit.location
           keyword "unit"
           e <- Toolkit.location
           pure (Const (newFC s e) UNIT ())

    char : Ola.Rule Raw.Expr
    char
      = do s <- Toolkit.location
           c <- Ola.char
           e <- Toolkit.location
           pure (Const (newFC s e) CHAR c)

    string : Ola.Rule Raw.Expr
    string
      = do s  <- Toolkit.location
           st <- Ola.string
           e  <- Toolkit.location
           pure (Const (newFC s e) STR st)

    int : Ola.Rule Raw.Expr
    int
      = do s  <- Toolkit.location
           st <- Ola.int
           e  <- Toolkit.location
           pure (Const (newFC s e) INT st)

    bool : Ola.Rule Raw.Expr
    bool
      = do st <- (gives "false" False <|> gives "true" True)
           pure (Const (fst st) BOOL (snd st))


uKind : Rule (FileContext, Unary)
uKind
    =  gives "left"   LEFT
   <|> gives "right"  RIGHT
   <|> gives "read"   READ
   <|> gives "close"  CLOSE
   <|> gives "not"    NOT
   <|> gives "size"   SIZE
   <|> gives "ord"    ORD
   <|> gives "chr"    CHR
   <|> gives "string"    STRO
   <|> gives "toString"    TOSTR

bKind : Rule (FileContext, Exprs.Binary)
bKind
    =  gives "and"   AND
   <|> gives "or"    OR
   <|> gives "lt"    LT
   <|> gives "lte"   LTE
   <|> gives "eq"    EQ
   <|> gives "gt"    GT
   <|> gives "gte"   GTE
   <|> gives "add"   ADD
   <|> gives "sub"   SUB
   <|> gives "mul"   MUL
   <|> gives "div"   DIV
   <|> gives "cons"  CONS

mutual
  fetch : Rule Expr
  fetch
    = do s <- Toolkit.location
         symbol "!"
         ex <- expr
         e <- Toolkit.location
         pure (Un (newFC s e) FETCH ex)

  array : Rule Expr
  array
    = do s <- Toolkit.location
         symbol "{"
         xs <- sepBy1 (symbol ",") expr
         symbol "}"
         e <- Toolkit.location
         -- Some rewriting to turn array literals into cons arrays.
         pure (foldr (cons e) (Null (newFC e e)) xs)
    where
      cons : Location -> Expr -> Expr -> Expr
      cons e x xs
        = let fc = { end := e} (getFC x)
          in Bin fc ARRAYCONS x xs

  unary : Rule Expr
  unary
    = do s <- Toolkit.location
         k <- uKind
         commit
         symbol "("
         ex <- expr
         symbol ")"
         e <- Toolkit.location
         pure (Un (newFC s e) (snd k) ex)

  binary : Rule Expr
  binary
    = do s <- Toolkit.location
         k <- bKind
         commit
         symbol "("
         ex <- expr
         symbol ","
         ey <- expr
         symbol ")"
         e <- Toolkit.location
         pure (Bin (newFC s e) (snd k) ex ey)

  kind : Rule HandleKind
  kind =  do keyword "fopen"; pure FILE
      <|> do keyword "popen"; pure PROCESS

  openE : Rule Expr
  openE
    = do s <- Toolkit.location
         k <- kind
         symbol "("
         ex <- expr
         symbol ","
         m <- mode
         symbol ")"
         e <- Toolkit.location

         pure (Un (newFC s e) (OPEN k m) ex)

  annot : Rule Expr
  annot
    = do s <- Toolkit.location
         symbol "("
         keyword "the"
         t <- type
         k <- expr
         symbol ")"
         e <- Toolkit.location
         pure (Un (newFC s e) (THE t) k)


  pair : Rule Expr
  pair
    = do s <- Toolkit.location
         keyword "pair"

         symbol "("
         l <- expr
         symbol ","
         r <- expr
         symbol ")"
         e <- Toolkit.location
         pure (Bin (newFC s e) PAIR l r)

  write : Rule Expr
  write
    = do s <- Toolkit.location
         keyword "write"
         symbol "("
         l <- expr
         symbol ","
         r <- expr
         symbol ")"
         e <- Toolkit.location
         pure (Bin (newFC s e) WRITE l r)

  call : Rule Expr
  call
    = do s <- Toolkit.location
         l <- var
         symbol "("
         r <- sepBy (symbol ",") expr
         symbol ")"
         e <- Toolkit.location
         pure (Call (newFC s e) l r)

  index : Rule Expr
  index
    = do s <- Toolkit.location
         keyword "index"
         symbol "("
         k <- expr
         symbol ","
         t <- Ola.int
         symbol ")"
         e <- Toolkit.location
         pure (Un (newFC s e) (INDEX t) k)

  ternary : Rule Expr
  ternary
    = do s <- Toolkit.location
         k <- (gives "cond" COND <|> gives "slice" SLICE)
         symbol "("
         c <- expr
         symbol ","
         l <- expr
         symbol ","
         r <- expr
         symbol ")"
         e <- Toolkit.location
         pure (Tri (newFC s e) (snd k) c l r)


  expr' : Rule Expr
  expr'
      = call <|> var <|> constants
            <|> fetch
            <|> array
            <|> unary
            <|> binary
            <|> annot
            <|> pair <|> write
            <|> openE
            <|> ternary
            <|> index

  export
  expr : Rule Expr
  expr
    =   symbol "(" *> expr' <* symbol ")"
    <|> expr'

-- [ EOF ]
