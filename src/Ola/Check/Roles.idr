|||
|||
||| Module    : Roles.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
module Ola.Check.Roles

import Toolkit.Data.Location
import Toolkit.Data.DList

import Data.Singleton

import Ola.Types
import Ola.Core

import Ola.Raw.AST
import Ola.Raw.Role

import Ola.Check.Common

import Ola.Terms.Vars
import Ola.Terms.Roles

%default total


-- ## Check

export
synth : {roles : List Ty.Role}
     -> (ctxt  : Context Ty.Role roles)
     -> (syn   : Role r)
              -> Ola (DPair Ty.Role (Role roles))
synth ctxt (R x)
  = lookup ctxt (MkRef emptyFC x)


-- [ EOF ]
