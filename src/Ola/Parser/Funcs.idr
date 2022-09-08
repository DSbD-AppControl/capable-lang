|||
|||
||| Module    : Funcs.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
module Ola.Parser.Funcs

import Data.List1
import Data.Maybe

import Ola.Lexer
import Ola.Parser.API

import Ola.Core
import Ola.Types

import Ola.Raw.Types
import Ola.Raw.Exprs
import Ola.Raw.Stmts
import Ola.Raw.Funcs

import Ola.Parser.Types
import Ola.Parser.Stmts

%default partial -- @TODO Make func parsing total.

total
arg : Rule (FileContext, (Ref, Raw.Ty))
arg
  = withLoc
      $ do n <- ref
           symbol ":"
           t <- type
           pure (n, t)

args : Rule (List (FileContext, Ref, Raw.Ty))
args
  = symbol "(" *> sepBy (symbol ",") arg <* symbol ")"

export
func : Rule (Ref, Raw.Func)
func
  = do s <- Toolkit.location
       keyword "func"
       n <- ref
       as <- args
       symbol "->"
       t <- type
       symbol "{"
       b <- body
       symbol "}"
       e <- Toolkit.location
       pure (n, Null (newFC s e) (FUNC as t (fst b) (snd b)))



-- [ EOF ]
