|||
|||
||| Module    : Capable.Types.Role
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
module Capable.Types.Role

import Decidable.Equality

import Capable.Bootstrap

%default total

namespace Ty
  ||| Roles will be distinguished as De Bruijn indices.
  public export
  data Role = MkRole


export
DecEq Role where
  decEq MkRole MkRole = Yes Refl

export
Show (IsVar ks MkRole) where
  show (V pos prf) = "(RoleVar \{show pos})"


public export
data Involved : (rs : List Role)
             -> (p : IsVar rs MkRole)
             -> (s : IsVar rs MkRole)
             -> (r : IsVar rs MkRole)
                        -> Type
  where
    Sends : (prfS : role = s)
                 -> Involved rs role s r

    Recvs : (prfR : role = r)
                 -> Involved rs role s r

    Skips : (prfSNot : Not (Equals Role (IsVar rs) role s))
         -> (prfRNot : Not (Equals Role (IsVar rs) role r))
                    -> Involved rs role s r

public export
involved : {rs : List Role}
        -> (p : IsVar rs MkRole)
        -> (s : IsVar rs MkRole)
        -> (r : IsVar rs MkRole)
        -> (contra  : Not (Equals Role (IsVar rs) s r))
                   -> Involved rs p s r
involved p s r contra with (Index.decEq p s)
  involved p p r contra | (Yes (Same Refl Refl)) = (Sends Refl)
  involved p s r contra | (No f) with (Index.decEq p r)
    involved p s p contra | (No f) | (Yes (Same Refl Refl)) = (Recvs Refl)
    involved p s r contra | (No f) | (No g) = (Skips f g)



public export
Roles : (rs : List Role) -> (ss : List Role) -> Type
Roles rs
  = DList Role (IsVar rs)


-- [ EOF ]
