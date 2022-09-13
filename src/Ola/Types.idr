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

%default total


public export
data Ty = B Base
        | R Role

Uninhabited (B b = R r) where
  uninhabited Refl impossible

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

{-
namespace API
  public export
  CHAR : Ty
  CHAR = B CHAR

  public export
  STR : Ty
  STR = B STR

  public export
  INT : Ty
  INT = B INT

  public export
  BOOL : Ty
  BOOL = B BOOL

  public export
  UNIT : Ty
  UNIT = B UNIT

  public export
  ARRAY : Base -> Nat -> Ty
  ARRAY b n = B $ ARRAY b n

  public export
  PAIR : Base -> Base -> Ty
  PAIR a b = B (PAIR a b)

  public export
  UNION : Base -> Base -> Ty
  UNION a b = B (UNION a b)

  public export
  HANDLE : HandleKind -> Ty
  HANDLE k = B (HANDLE k)

  public export
  REF : Base -> Ty
  REF t = B (REF t)

  public export
  FUNC : List Base -> Base -> Ty
  FUNC as r = B (FUNC as r)
-}
-- [ EOF ]
