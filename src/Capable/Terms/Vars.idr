||| Nameless representation.
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
||| We can make this more erasable but that is for later.
|||
module Capable.Terms.Vars

import public Toolkit.DeBruijn.Renaming

import Capable.Types

%default total

public export
Var : (context : List Ty)
   -> (type    : Ty)
              -> Type
Var = IsVar

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
