||| Aliases to make nameless representation of things easier to
||| write..
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
|||
module Capable.Terms.Vars

import public Toolkit.DeBruijn.Renaming

import Capable.Types

%default total

public export
TyVar : (context : List Ty.Base)
     -> (type    :      Ty.Base)
                -> Type
TyVar = IsVar

public export
RoleVar : (context : List Ty.Role)
       -> (type    :      Ty.Role)
                  -> Type
RoleVar = IsVar

-- [ EOF ]
