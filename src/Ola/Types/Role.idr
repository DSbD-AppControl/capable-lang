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


-- [ EOF ]
