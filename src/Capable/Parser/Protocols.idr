||| How to parse global types from the surface language.
|||
||| Copyright : COPYRIGHT
||| License   : see LICENSE
|||
|||
module Capable.Parser.Protocols

import Data.List1
import Data.Maybe
import Data.Either

import Capable.Core
import Capable.Types

import Capable.Lexer
import Capable.Parser.API

import Capable.Raw.AST

import Capable.Parser.Roles
import Capable.Parser.Types

%default total


end : Rule PROT
end
  = do s <- Toolkit.location
       keyword "end"
       e <- Toolkit.location
       pure (null STOP (newFC s e))

call : Rule PROT
call
  = do s <- Toolkit.location
       keyword "call"
       symbol "("
       r <- Capable.ref
       symbol ")"
       e <- Toolkit.location
       pure (null (CALLP (get r)) (newFC s e))

mutual
  rec : Rule PROT
  rec
    = do s <- Toolkit.location
         keyword "rec"
         symbol "("
         r <- Capable.ref
         symbol ")"
         symbol "."
         sesh <- protocol
         e <- Toolkit.location
         pure (un (RECP (get r)) (newFC s e) sesh)

  branch : Rule BRANCH
  branch
    = do s <- Toolkit.location
         l <- Capable.ref
         symbol "("
         t <- type
         symbol ")"
         symbol "."
         c <- protocol
         e <- Toolkit.location
         pure (bin (BRANCHP (get l)) (newFC s e) t c)

  choice : Rule PROT
  choice
    = do s <- Toolkit.location
         a <- role
         symbol "==>"
         b <- role
         symbol "["
         t <- type
         symbol "]"
         symbol "{"
         bs <- sepBy1 (symbol "|") branch
         symbol "}"
         e <- Toolkit.location
         pure (Branch CHOICE (newFC s e) $ a::b::t::head bs:: fromList (tail bs))

  export
  protocol : Rule PROT
  protocol
     =  end
    <|> call
    <|> choice
    <|> rec

-- [ EOF ]
