|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Ola.Parser.Roles

import Data.List1
import Data.Maybe
import Data.Either

import Ola.Core
import Ola.Types

import Ola.Lexer
import Ola.Parser.API

import Ola.Raw.AST

%default total

roleVar : Rule ROLE
roleVar
  = do r <- Ola.ref
       pure (null (ROLE (get r)) (span r))

||| Roles
export
role : Rule ROLE
role
    = roleVar

-- [ EOF ]
