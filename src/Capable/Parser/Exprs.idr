module Capable.Parser.Exprs

import Decidable.Equality

import Data.List.Views
import Data.List1

import Capable.Lexer
import Capable.Parser.API

import Capable.Core
import Capable.Types

import Capable.Raw.AST

import Capable.Parser.Types

import Debug.Trace

%default partial -- @TODO Make exprs parsing total.


buildSeq : EXPR -> List EXPR -> EXPR
buildSeq e xs with (snocList xs)
  buildSeq e [] | Empty
    = e
  buildSeq e (ys ++ [x]) | (Snoc x ys rec)
    = foldr fold x (e::ys)

    where fold : EXPR -> EXPR -> EXPR
          fold e acc
            = (bin SEQ (merge (getFC e) (getFC acc)) e acc)

export
var : Rule EXPR
var = do r <- Capable.ref
         pure (null (VAR (get r)) (span r))

hole : Rule EXPR
hole
  = do symbol "?"
       r <- Capable.ref
       pure (null (HOLE (get r)) (span r))

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

    char : Capable.Rule EXPR
    char
      = do s <- Toolkit.location
           c <- Capable.char
           e <- Toolkit.location
           pure (null (CONST CHAR c)(newFC s e))

    string : Capable.Rule EXPR
    string
      = do s  <- Toolkit.location
           st <- Capable.string
           e  <- Toolkit.location
           pure (null (CONST STR st) (newFC s e))

    int : Capable.Rule EXPR
    int
      = do s  <- Toolkit.location
           st <- Capable.int
           e  <- Toolkit.location
           pure (null (CONST INT st) (newFC s e))

    bool : Capable.Rule EXPR
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
         keyword "tuple"
         commit
         symbol "("
         l <- expr
         symbol ","
         r <- sepBy1 (symbol ",") expr
         symbol ")"
         e <- Toolkit.location
         pure (Branch TUPLE (newFC s e) (DVect.fromList $ l :: head r :: tail r))

  recor : Rule EXPR
  recor
    = do s <- Toolkit.location
         keyword "struct"
         symbol "["
         commit
         ty <- type
         symbol "]"
         s' <- Toolkit.location
         symbol "{"
         fs <- sepBy1 (symbol ",") field
         symbol "}"
         e <- Toolkit.location
         pure ( bin THE
                    (newFC s e)
                    ty
                    (Branch RECORD (newFC s' e) (DVect.fromList (head fs :: tail fs))))


    where field : Rule FIELDV
          field
            = do s <- Toolkit.location
                 l <- ref
                 symbol "="
                 commit
                 v <- expr
                 e <- Toolkit.location
                 pure (un (KV (get l)) (newFC s e) v)

  union : Rule EXPR
  union
    = do s <- Toolkit.location
         keyword "tag"
         commit
         symbol "["
         commit
         t <- ref
         symbol "]"
         symbol "("
         l <- expr
         symbol ")"
         e <- Toolkit.location
         pure (un (TAG (get t)) (newFC s e) l)

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

  getS : Rule EXPR
  getS
    = do s <- Toolkit.location
         keyword "get"
         symbol "["
         i <- ref
         symbol "]"
         symbol "("
         k <- expr
         symbol ")"
         e <- Toolkit.location
         pure (un (GETR (get i)) (newFC s e) k)

  getI : Rule EXPR
  getI
    = do s <- Toolkit.location
         keyword "get"
         symbol "["
         i <- int
         symbol "]"
         symbol "("
         k <- expr
         symbol ")"
         e <- Toolkit.location
         pure (un (GET i) (newFC s e) k)

  get : Rule EXPR
  get = getI <|> getS

  setI : Rule EXPR
  setI
    = do s <- Toolkit.location
         keyword "set"
         symbol "["
         i <- int
         symbol "]"
         symbol "("
         k <- expr
         symbol ","
         l <- expr
         symbol ")"
         e <- Toolkit.location
         pure (bin (SET i) (newFC s e) k l)

  setS : Rule EXPR
  setS
    = do s <- Toolkit.location
         keyword "set"
         symbol "["
         i <- ref
         symbol "]"
         symbol "("
         k <- expr
         symbol ","
         l <- expr
         symbol ")"
         e <- Toolkit.location
         pure (bin (SETR (get i)) (newFC s e) k l)

  set : Rule EXPR
  set = setI <|> setS

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
         keyword "mut"
         commit
         symbol "("
         l <- var
         symbol ","
         r <- expr
         symbol ")"
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
         cs <- some case'
         symbol "}"
         e <- Toolkit.location

         pure (Branch MATCH (newFC s e) (c :: head cs:: DVect.fromList (tail cs)))

    where case' : Rule CASE
          case'
            = do s <- Toolkit.location
                 keyword "when"
                 tag <- Capable.ref
                 symbol "("
                 n <- Capable.ref
                 symbol ")"
                 scope <- block
                 e <- Toolkit.location
                 pure (un (CASE (get tag) (get n)) (newFC s e) scope)

  let_ : String -> Stored ->  Rule EXPR
  let_ l sto
    = do s <- Toolkit.location
         keyword l
         commit
         v <- Capable.ref
         t <- optional (symbol ":" *> commit *> type)
         symbol "="
         ex <- expr
         symbol ";"
         e <- Toolkit.location
         scope <- seq
         maybe        (pure (bin (LET   sto (get v)) (newFC s e)    ex scope))
               (\ty => pure (tri (LETTY sto (get v)) (newFC s e) ty ex scope))
               t

  split : Rule EXPR
  split
    = do s <- Toolkit.location
         keyword "local"
         keyword "tuple"
         symbol "("
         commit
         l <- Capable.ref
         symbol ","
         rs <- sepBy1 (symbol ",") Capable.ref
         symbol ")"
         symbol "="
         c <- expr
         symbol ";"
         e <- Toolkit.location
         scope <- seq
         pure (bin (SPLIT (map get (l :: head rs :: tail rs)))
                   (newFC s e)
                   c
                   scope)

  seq : Rule EXPR
  seq
    = map (\xs => buildSeq (head xs) (tail xs))
          $ sepBy1 (symbol ";") expr
  export
  block : Rule EXPR
  block
    = do symbol "{"
         xs <- seq
         symbol "}"

         pure xs


  expr' : Rule EXPR
  expr'
      =   call
      <|> var
      <|> hole
      <|> constants
      <|> split
      <|> let_ "local" STACK
      <|> let_ "var"   HEAP
      <|> unary
      <|> binary
      <|> get
      <|> set
      <|> match
      <|> loop
      <|> cond
      <|> array
      <|> annot
      <|> pair
      <|> recor
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
      <|> (trace "\{show !Toolkit.location} split"     split)
      <|> (trace "\{show !Toolkit.location} mutate"    mutate)
      <|> (trace "\{show !Toolkit.location} un"        unary  )
      <|> (trace "\{show !Toolkit.location} bi"        binary )
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