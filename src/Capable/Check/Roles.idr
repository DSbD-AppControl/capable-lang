|||
||| Module    : Roles.idr
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Capable.Check.Roles

import Toolkit.Data.Location
import Toolkit.Data.DList

import Data.Singleton

import Capable.Types
import Capable.Core

import Capable.Raw.AST
import Capable.Raw.Role

import Capable.Check.Common

import Capable.Terms.Vars
import Capable.Terms.Roles

%default total


-- ## Check

export
synth : {roles : List Ty.Role}
     -> (ctxt  : Context Ty.Role roles)
     -> (syn   : Raw.Role.Role r)
              -> Capable (DPair Ty.Role (Role roles))
synth ctxt (R x)
  = lookup ctxt (MkRef emptyFC x)


-- [ EOF ]
