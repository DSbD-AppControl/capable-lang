|||
|||
module Ola.Parser.Funcs

import Data.List1
import Data.Maybe

import Toolkit.Data.DVect
import Ola.Lexer
import Ola.Parser.API

import Ola.Core
import Ola.Types

import Ola.Raw.AST

import Ola.Parser.Types
import Ola.Parser.Exprs

%default partial -- @TODO Make func parsing total.

total
arg : Rule ARG
arg
  = do s <- Toolkit.location
       n <- ref
       symbol ":"
       t <- type
       e <- Toolkit.location
       pure (un (ARG (get n)) (newFC s e) t)

args : Rule ARGS
args
  = do s <- Toolkit.location
       symbol "("
       as <- sepBy (symbol ",") arg
       symbol ")"
       e <- Toolkit.location
       pure (Branch ARGS (newFC s e) (fromList as))

export
func : Rule (Ref, FUNC)
func
  = do s <- Toolkit.location
       keyword "func"
       n <- ref
       as <- args
       symbol "->"
       t <- type
       b <- block
       e <- Toolkit.location
       pure (n, tri FUN (newFC s e) as t b)



-- [ EOF ]
