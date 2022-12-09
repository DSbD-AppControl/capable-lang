|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Capable.Parser.Roles

import Data.List1
import Data.Maybe
import Data.Either

import Capable.Core
import Capable.Types

import Capable.Lexer
import Capable.Parser.API

import Capable.Raw.AST

%default total

roleVar : Rule ROLE
roleVar
  = do r <- Capable.ref
       pure (null (ROLE (get r)) (span r))

||| Roles
export
role : Rule ROLE
role
    = roleVar

-- [ EOF ]
