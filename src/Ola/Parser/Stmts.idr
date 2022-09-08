|||
|||
||| Module    : Stmts.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
module Ola.Parser.Stmts

import Data.List1

import Ola.Lexer
import Ola.Parser.API

import Ola.Core
import Ola.Types

import Ola.Raw.Types
import Ola.Raw.Exprs
import Ola.Raw.Stmts

import Ola.Parser.Types
import Ola.Parser.Exprs

%default partial -- @TODO Make stmt parsing total.

mutual
  data S
    = Run    FileContext Expr
    | Print  FileContext Expr
    | Local  FileContext Ref (Maybe Raw.Ty) Expr
    | Var    FileContext Ref (Maybe Raw.Ty) Expr
    | While  FileContext Expr Block
    | Cond   FileContext Expr Block Block
    | Split  FileContext Expr Ref Ref
    | Match  FileContext Expr Ref Block Ref Block
    | Mutate FileContext Expr Expr

  data Block
    = ComputesReturnsNo (List1 S)
    | ComputesReturns   (List1 S) (FileContext, Expr)
    | Returns (FileContext, Expr)

mutate :  Rule S
mutate
  = do s <- Toolkit.location
       l <- expr
       symbol ":="
       r <- expr
       e <- Toolkit.location
       symbol ";"
       pure (Mutate (newFC s e) l r)

call : Rule S
call
  = do s <- Toolkit.location
       l <- var
       symbol "("
       r <- sepBy (symbol ",") expr
       symbol ")"
       e <- Toolkit.location
       symbol ";"
       pure (Run (newFC s e) $ Call (newFC s e) l r)

return : Rule (FileContext, Expr)
return
  = withLoc $ do keyword "return"
                 e <- expr
                 symbol ";"
                 pure e

print : Rule S
print
  = do res <- withLoc $ do keyword "print"
                           symbol "("
                           ex <- expr
                           symbol ")"
                           pure ex
       symbol ";"
       pure (Print (fst res) (snd res))

local : Rule S
local
  = do s <- Toolkit.location
       keyword "local"
       v <- Ola.ref
       t <- optional (symbol ":" *> type)
       symbol "="
       ex <- expr
       e <- Toolkit.location
       symbol ";"

       pure (Local (newFC s e)
                 v
                 t
                 ex)

var : Rule S
var
  = do s <- Toolkit.location
       keyword "var"
       v <- Ola.ref
       t <- optional (symbol ":" *> type)
       symbol "="
       ex <- expr
       e <- Toolkit.location
       symbol ";"

       pure (Var (newFC s e)
                 v
                 t
                 ex)

mutual

  while : Rule S
  while
    = do s <- Toolkit.location
         keyword "while"
         c <- expr
         symbol "{"
         b <- block
         symbol "}"
         e <- Toolkit.location
         pure (While (newFC s e) c b)

  cond : Rule S
  cond
    = do s <- Toolkit.location
         keyword "if"
         c <- expr
         symbol "{"
         lb <- block
         symbol "}"
         keyword "else"
         symbol "{"
         rb <- block
         symbol "}"
         e <- Toolkit.location
         pure (Cond (newFC s e) c lb rb)

  split : Rule S
  split
    = do s <- Toolkit.location
         keyword "split"
         c <- expr
         keyword "as"
         symbol "("
         l <- ref
         symbol ","
         r <- ref
         symbol ")"
         e <- Toolkit.location
         symbol ";"
         pure $ Split (newFC s e) c l r

  match : Rule S
  match
    = do s <- Toolkit.location
         keyword "match"
         c <- expr
         symbol "{"
         keyword "when"
         keyword "left"
         symbol "("
         l <- ref
         symbol ")"
         symbol "{"
         lb <- block
         symbol "}"
         keyword "when"
         keyword "right"
         symbol "("
         r <- ref
         symbol ")"
         symbol "{"
         rb <- block
         symbol "}"
         symbol "}"
         e <- Toolkit.location
         pure $ Match (newFC s e) c l lb r rb

  stmt : Rule S
  stmt
    = mutate <|> print
             <|> call
             <|> local
             <|> var
             <|> while
             <|> cond
             <|> split
             <|> match

  block : Rule Block
  block
      = computeReturns <|> computeReturnsNot <|> returns
    where
      returns : Rule Block
      returns
        = pure (Returns !(return))

      computeReturns : Rule Block
      computeReturns
        = do ss <- some stmt
             re <- return
             pure (ComputesReturns ss re)

      computeReturnsNot : Rule Block
      computeReturnsNot
        = do ss <- some stmt
             pure (ComputesReturnsNo ss)


mutual

  fold : S -> Raw.Stmt -> Raw.Stmt
  fold (Run fc e)
    = Un fc (RUN e)

  fold (Print fc s)
    = Un fc (PRINT s)

  fold (Local fc v t e)
    = Un fc (LET v t e)
  fold (Var fc v t e)
    = Un fc (VAR v t e)

  fold (While fc c b)
    = Bin fc (WHILE c)
             (foldBlock b)

  fold (Cond fc c tt ff)
    = Tri fc (COND c)
             (foldBlock tt)
             (foldBlock ff)

  fold (Split fc c a b)
    = Un fc (SPLIT c a b)

  fold (Match fc c l lb r rb)
    = Tri fc (MATCH c l r)
             (foldBlock lb)
             (foldBlock rb)


  fold (Mutate fc v e)
    = Un fc (MUTATE v e)


  foldr' : List1 S -> Raw.Stmt -> Raw.Stmt
  foldr' (head ::: tail) x
    = fold head $ foldr fold x tail


  foldBlock : Block -> Raw.Stmt
  foldBlock (ComputesReturnsNo xs)
    = foldr' xs (Null emptyFC END)

  foldBlock (ComputesReturns xs (fc,e))
    = foldr' xs (Null emptyFC (RET e))

  foldBlock (Returns (fc,e))
    = (Null emptyFC (RET e))


  foldBlock' : Block -> (Raw.Stmt, Raw.Expr)
  foldBlock' (ComputesReturnsNo xs)
    = ( foldr' xs (Null emptyFC END)
      , Const emptyFC UNIT ())

  foldBlock' (ComputesReturns xs (fc,e))
    = ( foldr' xs (Null emptyFC END)
      , e)

  foldBlock' (Returns (fc,e))
    = MkPair (Null emptyFC END)
             e


export
body : Rule (Raw.Stmt, Raw.Expr)
body
  = pure (foldBlock' (!block))

-- [ EOF ]
