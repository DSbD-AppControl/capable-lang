||| Roles in a protocol.
|||
||| Copyright : COPYRIGHT
||| License   : see LICENSE
|||
module Capable.Types.Role

import Decidable.Equality
import Toolkit.Decidable.Do

import Capable.Bootstrap

%default total

namespace Ty
  ||| Roles will be distinguished as De Bruijn indices.
  public export
  data Role = MkRole String

namespace DeBruijn
  public export
  Role : (rs : List Role) -> Role -> Type
  Role = IsVar


export
DecEq Role where
  decEq (MkRole a) (MkRole b)
    = decDo $ do Refl <- decEq a b `otherwise` (\Refl => Refl)
                 pure Refl

--export
--Show (IsVar ks MkRole) where
--  show (V pos prf) = "(RoleVar \{show pos})"

public export
REquals : (rs  : List Role)
       -> {a,b : Role}
       -> (x  : Role rs a)
       -> (y  : Role rs b)
       -> Type
REquals rs x y = Indexed.Equals Role (Role rs) x y

public export
data Involved : (rs : List Role)
             -> (p : Role rs x)
             -> (s : Role rs y)
             -> (r : Role rs z)
                        -> Type
  where
    Sends : (prfS : role = s)
                 -> Involved rs role s r

    Recvs : (prfR : role = r)
                 -> Involved rs role s r

    Skips : (prfSNot : (REquals rs role s) -> Void)
         -> (prfRNot : (REquals rs role r) -> Void)
                    -> Involved rs role s r

public export
involved : {rs : List Role}
        -> {x,y,z : Role}
        -> (p : Role rs x)
        -> (s : Role rs y)
        -> (r : Role rs z)
--        -> (contra  : Not (REquals rs s r))
                   -> Involved rs p s r
involved p s r with (Index.decEq p s)
  involved s s r | (Yes (Same Refl Refl))
    = Sends Refl
  involved p s r | (No f) with (Index.decEq p r)
    involved p s p | (No f) | (Yes (Same Refl Refl))
      = Recvs Refl
    involved p s r | (No f) | (No g)
      = Skips f g

public export
Roles : (rs : List Role) -> (ss : List Role) -> Type
Roles rs = DList Role (Role rs)

-- [ EOF ]
