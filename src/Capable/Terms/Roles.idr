||| Roles as terms because we want to mirror real programmes.
|||
||| Module    : Roles.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
module Capable.Terms.Roles

import public Data.List.Elem

import public Toolkit.Data.DList

import public Capable.Types
import        Capable.Terms.Vars

%default total

public export
Role : (context : List Ty.Role)
    -> (type    :      Ty.Role)
               -> Type
Role = RoleVar

-- [ EOF ]
