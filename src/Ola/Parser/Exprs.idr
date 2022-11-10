module Ola.Parser.Exprs

import Decidable.Equality

import Data.List.Views
import Data.List1

import Ola.Lexer
import Ola.Parser.API

import Ola.Core
import Ola.Types

import Ola.Raw.AST

import Ola.Parser.Types

import Debug.Trace

%default partial -- @TODO Make exprs parsing total.


export
var : Rule EXPR
var = do r <- Ola.ref
         pure (null (VAR (get r)) (span r))


constants : Rule EXPR
constants
    =      unit
       <|> char <|> string <|> int <|> bool
  where
    unit : Rule EXPR
    unit
      = do s <- Toolkit.location
           keyword "unit"
           e <- Toolkit.location
           pure (null (CONST UNIT ()) (newFC s e))

    char : Ola.Rule EXPR
    char
      = do s <- Toolkit.location
           c <- Ola.char
           e <- Toolkit.location
           pure (null (CONST CHAR c)(newFC s e))

    string : Ola.Rule EXPR
    string
      = do s  <- Toolkit.location
           st <- Ola.string
           e  <- Toolkit.location
           pure (null (CONST STR st) (newFC s e))

    int : Ola.Rule EXPR
    int
      = do s  <- Toolkit.location
           st <- Ola.int
           e  <- Toolkit.location
           pure (null (CONST INT st) (newFC s e))

    bool : Ola.Rule EXPR
    bool
      =   givesWithLoc "false" (null (CONST BOOL False))
      <|> givesWithLoc "true"  (null (CONST BOOL True))

uKind : Rule BuiltinUnOps
uKind
    =  gives "read"      READ
   <|> gives "close"     CLOSE
   <|> gives "not"       NOT
   <|> gives "size"      SIZE
   <|> gives "ord"       ORD
   <|> gives "chr"       CHR
   <|> gives "string"    STRO
   <|> gives "toString"  TOSTR
   <|> gives "print"     PRINT


bKind : Rule BuiltinBinOps
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
   <|> gives "write"   WRITE
   <|> gives "strCons"  STRCONS

mutual
  fetch : Rule EXPR
  fetch
    = do s <- Toolkit.location
         symbol "!"
         commit
         ex <- expr
         e <- Toolkit.location
         pure (un (BUN FETCH) (newFC s e) ex)

  array : Rule EXPR
  array
    = do s <- Toolkit.location
         symbol "{"
         xs <- sepBy1 (symbol ",") expr
         symbol "}"
         e <- Toolkit.location
         -- Some rewriting to turn array literals into cons arrays.
         pure (foldr (cons e) (null NIL (newFC e e)) xs)
    where
      cons : Location -> EXPR -> EXPR -> EXPR
      cons e x xs
        = let fc = { end := e} (getFC x)
          in bin CONS fc x xs

  unary : Rule EXPR
  unary
    = do s <- Toolkit.location
         k <- uKind
         commit
         symbol "("
         ex <- expr
         symbol ")"
         e <- Toolkit.location
         pure (un (BUN k) (newFC s e) ex)


  binary : Rule EXPR
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
         pure (bin (BBIN k) (newFC s e) ex ey)


  kind : Rule HandleKind
  kind =  do keyword "fopen"; pure FILE
      <|> do keyword "popen"; pure PROCESS

  openE : Rule EXPR
  openE
    = do s <- Toolkit.location
         k <- kind
         commit
         symbol "("
         ex <- expr
         symbol ","
         m <- mode
         symbol ")"
         e <- Toolkit.location

         pure (un (BUN (OPEN k m)) (newFC s e) ex)

  annot : Rule EXPR
  annot
    = do s <- Toolkit.location
         keyword "the"
         commit
         symbol "("
         t <- type
         k <- expr
         symbol ")"
         e <- Toolkit.location
         pure (bin THE (newFC s e) t k)


  pair : Rule EXPR
  pair
    = do s <- Toolkit.location
         keyword "pair"
         commit
         symbol "("
         l <- expr
         symbol ","
         r <- expr
         symbol ")"
         e <- Toolkit.location
         pure (bin PAIR (newFC s e) l r)

  union : Rule EXPR
  union
    = do s <- Toolkit.location
         k <- (keyword "left" *> pure LEFT <|> keyword "right" *> pure RIGHT)
         commit
         symbol "("
         l <- expr
         symbol ")"
         e <- Toolkit.location
         pure (un k (newFC s e) l)

  call : Rule EXPR
  call
    = do s <- Toolkit.location
         l <- var
         a <- args
         e <- Toolkit.location
         pure (Branch CALL (newFC s e) (l::fromList a))

    where args : Rule (List EXPR)
          args =  symbol "(" *> symbol ")" *> pure Nil
              <|> do as <- symbol "(" *> sepBy1 (symbol ",") expr <* symbol ")"
                     pure (forget as)



  index : Rule EXPR
  index
    = do s <- Toolkit.location
         keyword "index"

         symbol "("
         k <- expr
         symbol ","
         t <- expr
         symbol ")"
         e <- Toolkit.location
         pure (bin IDX (newFC s e) t k)

  slice : Rule EXPR
  slice
    = do s <- Toolkit.location
         keyword "slice"

         symbol "("
         c <- expr
         symbol ","
         l <- expr
         symbol ","
         r <- expr
         symbol ")"
         e <- Toolkit.location
         pure (tri SLICE (newFC s e) c l r)

  mutate :  Rule EXPR
  mutate
    = do s <- Toolkit.location
         keyword "set"
         commit
         l <- expr
         keyword "to"
         r <- expr
         e <- Toolkit.location
         pure (bin (BBIN MUT) (newFC s e) l r)

  cond : Rule EXPR
  cond
    = do s <- Toolkit.location
         keyword "if"
         commit
         c <- expr
         lb <- block
         keyword "else"
         rb <- block
         e <- Toolkit.location
         pure (tri COND (newFC s e) c lb rb)

  loop : Rule EXPR
  loop
    = do s <- Toolkit.location
         keyword "loop"
         commit
         b <- block
         keyword "until"
         c <- expr
         e <- Toolkit.location
         pure (bin LOOP (newFC s e) b c)

  match : Rule EXPR
  match
    = do s <- Toolkit.location
         keyword "match"
         commit
         c <- expr
         symbol "{"
         keyword "when"
         keyword "left"
         symbol "("
         l <- Ola.ref
         symbol ")"
         lb <- block
         keyword "when"
         keyword "right"
         symbol "("
         r <- Ola.ref
         symbol ")"
         rb <- block
         symbol "}"
         e <- Toolkit.location
         pure (tri (MATCH (get l) (get r)) (newFC s e) c lb rb)

  let_ : String -> Stored ->  Rule EXPR
  let_ l sto
    = do s <- Toolkit.location
         keyword l
         commit
         v <- Ola.ref
         t <- optional (symbol ":" *> type)
         symbol "="
         ex <- expr
         keyword "in"
         e <- Toolkit.location
         scope <- (block)
         maybe        (pure (bin (LET   sto (get v)) (newFC s e)    ex scope))
               (\ty => pure (tri (LETTY sto (get v)) (newFC s e) ty ex scope))
               t
  split : Rule EXPR
  split
    = do s <- Toolkit.location
         keyword "split"
         commit
         c <- expr
         keyword "as"
         symbol "("
         l <- Ola.ref
         symbol ","
         r <- Ola.ref
         symbol ")"
         e <- Toolkit.location
         keyword "in"
         e <- Toolkit.location
         scope <- block
         pure (bin (SPLIT (get l) (get r)) (newFC s e) c scope)

  export
  block : Rule EXPR
  block
    = do s <- Toolkit.location
         symbol "{"
         xs <- sepBy1 (symbol ";") expr
         symbol "}"
         e <- Toolkit.location
         pure (build (head xs) (tail xs))

    where fold : EXPR -> EXPR -> EXPR
          fold e acc
            = (bin SEQ (merge (getFC e) (getFC acc)) e acc)

          build : EXPR -> List EXPR -> EXPR
          build e xs with (snocList xs)
            build e [] | Empty
              = e
            build e (ys ++ [x]) | (Snoc x ys rec)
              = foldr fold x (e::ys)

  expr' : Rule EXPR
  expr'
      =   call
      <|> var
      <|> constants
      <|> let_ "local" STACK
      <|> let_ "var"   HEAP
      <|> unary
      <|> binary
      <|> split
      <|> match
      <|> loop
      <|> cond
      <|> array
      <|> annot
      <|> pair
      <|> union
      <|> openE
      <|> slice
      <|> index
      <|> fetch
      <|> mutate

  exprT : Rule EXPR
  exprT
      =   (trace "\{show !Toolkit.location} call"      call)
      <|> (trace "\{show !Toolkit.location} var"       var)
      <|> (trace "\{show !Toolkit.location} constants" constants)
      <|> (trace "\{show !Toolkit.location} local"     $ let_ "local" STACK)
      <|> (trace "\{show !Toolkit.location} new"       $ let_ "var"   HEAP)
      <|> (trace "\{show !Toolkit.location} mutate"    mutate)
      <|> (trace "\{show !Toolkit.location} un"        unary  )
      <|> (trace "\{show !Toolkit.location} bi"        binary )
      <|> (trace "\{show !Toolkit.location} split"     split)
      <|> (trace "\{show !Toolkit.location} match"     match)
      <|> (trace "\{show !Toolkit.location} loop"      loop   )
      <|> (trace "\{show !Toolkit.location} if"        cond   )
      <|> (trace "\{show !Toolkit.location} ar"        array  )
      <|> (trace "\{show !Toolkit.location} the"       annot  )
      <|> (trace "\{show !Toolkit.location} pait"      pair   )
      <|> (trace "\{show !Toolkit.location} union"     union  )
      <|> (trace "\{show !Toolkit.location} open"      openE  )
      <|> (trace "\{show !Toolkit.location} slice"     slice  )
      <|> (trace "\{show !Toolkit.location} index"     index  )
      <|> (trace "\{show !Toolkit.location} !"         fetch  )


  export
  expr : Rule EXPR
  expr
    = expr'

-- [ EOF ]
