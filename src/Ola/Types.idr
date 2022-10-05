|||
|||
||| Module    : Ola.Types
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
module Ola.Types

import Decidable.Equality

import Toolkit.Decidable.Informative

import public Ola.Types.Base
import public Ola.Types.Role
import public Ola.Types.Session

%default total


public export
data Ty = B Base
        | R Role
        | G (Global ks rs)
        | L (Local ks rs)

Uninhabited (B b = R r) where
  uninhabited Refl impossible

{- Need to reinstate
export
DecEq Ty where
  -- [ NOTE ] base type
  decEq (B x) b with (b)
    decEq (B x) b | (B y) with (decEq x y)
      decEq (B x) b | (B x) | (Yes Refl)
        = Yes Refl
      decEq (B x) b | (B y) | (No contra)
        = No (\Refl => contra Refl)

    decEq (B x) b | (R y)
      = No absurd

  -- [ NOTE ] Roles
  decEq (R x) b with (b)
    decEq (R x) b | (B y)
      = No (negEqSym absurd)

    decEq (R x) b | (R y) with (decEq x y)
      decEq (R x) b | (R x) | (Yes Refl)
        = Yes Refl
      decEq (R x) b | (R y) | (No contra)
        = No (\Refl => contra Refl)

public export
data EqualNot : (x,y : Ty)
                 -> Type
  where
    BaseNotEqual : (prf : x = y -> Void)
                      -> EqualNot (B x) (B y)

    ExpectedBase : EqualNot (B b) not_base

    ExpectedRole : EqualNot (R r)  not_role

export
decEq : (x,y : Ty)
            -> DecInfo (EqualNot x y)
                       (Equal    x y)

-- [ NOTE ] Base types
decEq (B x) y with (y)
  decEq (B x) y | (B z) with (decEq x z)
    decEq (B x) y | (B x) | (Yes Refl)
      = Yes Refl

    decEq (B x) y | (B z) | (No contra)
      = No (BaseNotEqual contra)
           (\Refl => contra Refl)


  decEq (B x) y | (R z)
    = No ExpectedBase
         absurd

-- [ NOTE ] Roles
decEq (R x) y with (y)
  decEq (R x) y | (B z)
    = No ExpectedRole
         (negEqSym absurd)

  decEq (R x) y | (R z) with (decEq x z)
    decEq (R x) y | (R x) | (Yes Refl)
      = Yes Refl

    decEq (R x) y | (R z) | (No contra)
      = No ExpectedRole
           (\Refl => contra Refl)
-}

-- [ EOF ]
