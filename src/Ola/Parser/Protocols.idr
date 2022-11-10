||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
module Ola.Parser.Protocols

import Data.List1
import Data.Maybe
import Data.Either

import Ola.Core
import Ola.Types

import Ola.Lexer
import Ola.Parser.API

import Ola.Raw.AST

import Ola.Parser.Roles
import Ola.Parser.Types

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
       r <- Ola.ref
       symbol ")"
       e <- Toolkit.location
       pure (null (CALLP (get r)) (newFC s e))

mutual
  rec : Rule PROT
  rec
    = do s <- Toolkit.location
         keyword "rec"
         symbol "("
         r <- Ola.ref
         symbol ")"
         symbol "."
         sesh <- protocol
         e <- Toolkit.location
         pure (un (RECP (get r)) (newFC s e) sesh)

  branch : Rule BRANCH
  branch
    = do s <- Toolkit.location
         l <- Ola.ref
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
         symbol "{"
         bs <- sepBy1 (symbol "|") branch
         symbol "}"
         e <- Toolkit.location
         pure (Branch CHOICE (newFC s e) $ a::b::head bs:: fromList (tail bs))

  export
  protocol : Rule PROT
  protocol
     =  end
    <|> call
    <|> choice
    <|> rec

-- [ EOF ]
