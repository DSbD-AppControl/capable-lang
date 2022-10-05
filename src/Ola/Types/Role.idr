|||
|||
||| Module    : Ola.Types.Role
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
module Ola.Types.Role

import Decidable.Equality

import Toolkit.Decidable.Do

%default total

namespace Ty
  ||| Roles will be distinguished as De Bruijn indices.
  public export
  data Role = MkRole


export
DecEq Role where
  decEq MkRole MkRole = Yes Refl


public export
data Involved : (p, s, r : Role)
                        -> Type
  where
    Sends : (prfS : role = s)
                 -> Involved role s r

    Recvs : (prfR : role = r)
                 -> Involved role s r

    Skips : (prfSNot : Not (role = s))
         -> (prfRNot : Not (role = r))
                    -> Involved role s r

public export
involved : DecEq role
        => (p, s, r : Role)
        -> (contra  : Not (s = r))
                   -> Involved p s r
involved p s r contra with (decEq p s)
  involved p p r contra | (Yes Refl) = (Sends Refl)
  involved p s r contra | (No f) with (decEq p r)
    involved p s p contra | (No f) | (Yes Refl) = (Recvs Refl)
    involved p s r contra | (No f) | (No g) = (Skips f g)

-- [ EOF ]
