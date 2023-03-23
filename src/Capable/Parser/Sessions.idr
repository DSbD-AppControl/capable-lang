module Capable.Parser.Sessions

import Decidable.Equality

import Data.List.Views
import Data.List1

import Capable.Lexer
import Capable.Parser.API

import Capable.Core
import Capable.Types

import Capable.Raw.AST

import Capable.Parser.Roles
import Capable.Parser.Types
import Capable.Parser.Exprs
import Capable.Parser.Funcs

import Debug.Trace

%default partial -- @TODO Make exprs parsing total.

-- @TODO Limitations on language expressiveness
--       1. must wrap values as local vars to cross the language divide
-- Add split to session expressoins

hole : Rule (AST EXPRSESH)
hole
  = do symbol "?"
       r <- Capable.ref
       pure (null (HOLE_SESH (get r)) (span r))

end : Rule (AST EXPRSESH)
end
  = do s <- Toolkit.location
       keyword "end"
       symbol "("
       v <- Exprs.expr
       symbol ")"
       e <- Toolkit.location
       pure (un END_SESH (newFC s e) v)

crash : Rule (AST EXPRSESH)
crash
  = do s <- Toolkit.location
       keyword "crash"
       symbol "("
       v <- Exprs.expr
       symbol ")"
       e <- Toolkit.location
       pure (un CRASH_SESH (newFC s e) v)

mutual
  send : Rule (AST EXPRSESH)
  send
    = do s <- Toolkit.location
         keyword "send"
         commit
         r <- role
         p <- expr
         keyword "catch"
         er <- Sessions.block
         n <- Sessions.expr
         e <- Toolkit.location
         pure (Branch SEND (newFC s e) [r,p,n,er])

  read : Rule (AST EXPRSESH)
  read
      = do s <- Toolkit.location
           keyword "recv"
           commit
           r <- role
           symbol "{"
           os <- some offer
           symbol "}"
           keyword "catch"
           err <- Sessions.block
           e <- Toolkit.location
           pure (Branch READ (newFC s e) (r::err:: head os :: (DVect.fromList (tail os))))

    where offer : Rule (AST OFFER)
          offer
            = do s <- Toolkit.location
                 keyword "when"
                 tag <- Capable.ref
                 symbol "("
                 n <- Capable.ref
                 symbol ")"
                 scope <- Sessions.block
                 e <- Toolkit.location
                 pure (un (OFFER (get tag)
                                 (get n))
                          (newFC s e)
                          scope)


  call : Rule (AST EXPRSESH)
  call
    = do s <- Toolkit.location
         keyword "call"
         symbol "("
         l <- ref
         symbol ")"
         e <- Toolkit.location
         pure (null (CALL_SESH (get l)) (newFC s e))

  split : Rule (AST EXPRSESH)
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
         c <- Exprs.expr
         symbol ";"
         e <- Toolkit.location
         scope <- Sessions.block
         pure (bin (SPLIT_SESH (map get (l :: head rs :: tail rs)))
                   (newFC s e)
                   c
                   scope)


  seq : Rule (AST EXPRSESH)
  seq
    = do s <- Toolkit.location
         ex <- Exprs.expr
         symbol ";"
         rest <- Sessions.expr
         e <- Toolkit.location
         pure (Branch SEQ_SESH (newFC s e) [ex,rest])


  block : Rule (AST EXPRSESH)
  block
    = do symbol "{"
         xs <- expr
         symbol "}"
         pure xs

  let_ : String -> Stored ->  Rule (AST EXPRSESH)
  let_ l sto
    = do s <- Toolkit.location
         keyword l
         commit
         v <- Capable.ref
         t <- optional (symbol ":" *> commit *> type)
         symbol "="
         ex <- Exprs.expr
         symbol ";"
         e <- Toolkit.location
         scope <- Sessions.expr
         maybe        (pure (bin (LET_SESH   sto (get v)) (newFC s e)    ex scope))
               (\ty => pure (tri (LETTY_SESH sto (get v)) (newFC s e) ty ex scope))
               t

  rec : Rule (AST EXPRSESH)
  rec
    = do s <- Toolkit.location
         keyword "rec"
         l <- Capable.ref
         scope <- Sessions.block
         e <- Toolkit.location
         pure (un (LETREC_SESH (get l)) (newFC s e) scope)

  expr' : Rule (AST EXPRSESH)
  expr'
    =   call
    <|> crash
    <|> end
    <|> hole
    <|> seq
    <|> split
    <|> let_ "local" STACK
    <|> let_ "var"   HEAP
    <|> rec
    <|> send
    <|> read


  expr : Rule (AST EXPRSESH)
  expr = expr'


export
session : Rule (Ref, AST SESH)
session
  = do s <- Toolkit.location
       keyword "session"
       commit
       n <- ref
       symbol "<"
       p <- ref
       keyword "as"
       r <- role
       symbol ">"
       as <- args
       symbol "->"
       t <- type
       b <- block
       e <- Toolkit.location
       pure (n, Branch (SESH (get p)) (newFC s e) [r,as,t,b])

-- [ EOF ]
