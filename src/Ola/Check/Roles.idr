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

import Ola.Raw.Roles
import Ola.Check.Common

import Ola.Terms.Vars
import Ola.Terms.Roles

%default total


-- ## Check

export
roleCheck : {roles : List Ty.Role}
         -> (ctxt  : Context Ty.Role roles)
         -> (syn   : Raw.Role)
                  -> Ola (DPair Ty.Role (Role roles))
roleCheck ctxt (RoleDef _)
  = pure (_ ** RoleDef)

roleCheck ctxt (RoleRef x)
  = do prf <- embedAtInfo
                  (span x)
                  (NotBound x)
                  (Lookup.lookup (get x) ctxt)
       let (r ** (loc ** prfN)) = deBruijn prf
       pure (r ** RoleVar (V loc prfN))

-- [ EOF ]
