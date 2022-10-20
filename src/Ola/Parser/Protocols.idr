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

import Ola.Raw.Roles
import Ola.Raw.Types
import Ola.Raw.Protocols

import Ola.Parser.Roles
import Ola.Parser.Types

%default total


end : Rule Raw.Protocol
end
  = do s <- Toolkit.location
       keyword "end"
       e <- Toolkit.location
       pure (Null (newFC s e) END)

call : Rule Raw.Protocol
call
  = do s <- Toolkit.location
       keyword "call"
       symbol "("
       r <- Ola.ref
       symbol ")"
       e <- Toolkit.location
       pure (Null (newFC s e) (CALL r))

mutual
  rec : Rule Raw.Protocol
  rec
    = do s <- Toolkit.location
         keyword "rec"
         symbol "("
         r <- Ola.ref
         symbol ")"
         symbol "."
         sesh <- protocol
         e <- Toolkit.location
         pure (Un (newFC s e) (REC r) sesh)

  branch : Rule (String, Raw.Ty, Raw.Protocol)
  branch
    = do l <- Ola.ref
         symbol "("
         t <- type
         symbol ")"
         symbol "."
         s <- protocol
         pure (get l,t,s)

  choice : Rule Raw.Protocol
  choice
    = do s <- Toolkit.location
         a <- role
         symbol "==>"
         b <- role
         symbol "{"
         bs <- sepBy1 (symbol "|") branch
         symbol "}"
         e <- Toolkit.location
         pure (N1 (newFC s e) (CHOICE a b) bs)

  export
  protocol : Rule Raw.Protocol
  protocol
     =  end
    <|> call
    <|> choice
    <|> rec

-- [ EOF ]
