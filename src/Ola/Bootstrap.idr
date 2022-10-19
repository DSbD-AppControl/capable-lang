module Ola.Bootstrap

import public Decidable.Equality
import public Toolkit.Decidable.Equality.Indexed
import public Toolkit.DeBruijn.Renaming
import public Toolkit.Data.List.AtIndex

%default total

export
Uninhabited (AtIndex x [] n) where
  uninhabited at impossible

public export
irrelevantAtIndex : (p, q : AtIndex x xs n) -> p === q
irrelevantAtIndex Here Here = Refl
irrelevantAtIndex (There p) (There q) = cong There (irrelevantAtIndex p q)

export
Uninhabited (IsVar [] x) where
  uninhabited (V n prf) = void (uninhabited prf)

export
DecEq (IsVar ctxt type) where
  decEq (V m p) (V n q) with (decEq m n)
    decEq (V .(m) p) (V m q) | Yes Refl
      = Yes (rewrite irrelevantAtIndex p q in Refl)
    _ | No neq = No (\case Refl => neq Refl)


export
{kind : Type} -> {ctxt : List kind} -> DecEq kind => DecEqIdx kind (IsVar ctxt) where
  decEq x y Refl with (Equality.decEq x y)
    decEq x x Refl | (Yes Refl)
      = Yes (Same Refl Refl)
    decEq x y Refl | (No contra)
      = No (\(Same Refl Refl) => contra Refl)

-- [ EOF ]
