|||
|||
||| Module    : Parser.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
module Ola.Parser

import Data.List1

import Ola.Lexer
import Ola.Parser.API

import Ola.Core
import Ola.Types

%default total

namespace AST
  export
  data Expr : Type where -- @TODO

  export
  data Stmt : Type where -- @TODO

  export
  data Prog : Type where -- @TODO
  export
  setSource : String -> Prog -> Prog


expr : Rule Expr

statment : Rule Stmt

program : Rule Prog

namespace Ola

  export
  fromFile : (fname : String)
                   -> Ola Prog
  fromFile fname
    = do ast <- parseFile (\p => Parse (PError fname p))
                Ola.Lexer
                program
                fname
         pure (setSource fname ast)


-- [ EOF ]
