|||
|||
||| Module    : Roles.idr
||| Copyright : (c) Jan de Muijnck-Hughes
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

import Ola.Raw.Roles

%default total

roleVar : Rule Raw.Role
roleVar
  = do r <- Ola.ref
       pure (RoleRef r)

||| Roles
export
role : Rule Raw.Role
role
    = roleVar

-- [ EOF ]
