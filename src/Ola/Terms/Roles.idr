||| Roles as terms because we want to mirror real programmes.
|||
||| Module    : Roles.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
module Ola.Terms.Roles

import public Data.List.Elem

import public Toolkit.Data.DList

import public Ola.Types
import        Ola.Terms.Vars

%default total

public export
Role : (context : List Ty.Role)
    -> (type    :      Ty.Role)
               -> Type
Role = RoleVar
{-
||| Roles as a Term.
|||
public export
data Role : (context : List Ty.Role)
         -> (type    :      Ty.Role)
                  -> Type
  where
    RoleDef : Role ctxt MkRole

    RoleVar : RoleVar ctxt role
           -> Role    ctxt role
-}
-- [ EOF ]
