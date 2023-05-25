module Capable.Bootstrap

import public Toolkit.Data.DList
import public Toolkit.Data.DList.Elem
import Toolkit.Data.DList.All

import public Toolkit.DeBruijn.Context
import public Toolkit.DeBruijn.Context.Item
import public Toolkit.DeBruijn.Renaming

import public Decidable.Equality
import public Toolkit.Decidable.Equality.Indexed
import public Toolkit.Decidable.Informative
import public Toolkit.Data.List.AtIndex
import Text.PrettyPrint.Prettyprinter

%default total

export
reflect : (ctxt  : Context a rs)
       -> (loc   : IsVar rs l)
                -> String
reflect [] (V _ Here) impossible
reflect [] (V _ (There later)) impossible

reflect ((I name x) :: rest) (V 0 prf) = name
reflect (elem :: rest) (V (S k) (There later)) = reflect rest (V k later)

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
Pretty (IsVar ctxt type) where
  pretty (V n _) = pretty n

export
Show (IsVar ctxt type) where
  show = (show . annotate () . pretty)


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


export
decidable : Lazy b -> Lazy (a -> b) -> Dec a -> b
decidable _ y (Yes prf)
  = y prf
decidable x _ (No _)
  = x


export
dec2Maybe : Dec a -> Maybe a
dec2Maybe (Yes prf) = Just prf
dec2Maybe (No  _)   = Nothing

export
decInfo2Maybe : DecInfo e a -> Maybe a
decInfo2Maybe (Yes prf) = Just prf
decInfo2Maybe (No _ _)   = Nothing

export
decidableI : Lazy (e -> b)
          -> Lazy (a -> b)
          -> DecInfo e a
          -> b
decidableI _ f (Yes prf)
  = f prf
decidableI f _ (No prf _)
  = f prf


namespace List
  public export
  data Union : (xs,ys,zs : List a) -> Type where
    End : Union Nil ys ys
    Pos : Elem x ys
       -> Union     xs  ys zs
       -> Union (x::xs) ys zs
    Neg : Not (Elem x ys)
       -> Union     xs  ys     zs
       -> Union (x::xs) ys (x::zs)

  export
  union : DecEq a
       => (xs,ys : List a)
                -> DPair (List a) (Union xs ys)

  union [] ys
    = (ys ** End)

  union (x :: xs) ys with (union xs ys)
    union (x :: xs) ys | (zs ** prf) with (isElem x ys)
      union (x :: xs) ys | (zs ** prf) | (Yes prfR)
        = (zs ** Pos prfR prf)
      union (x :: xs) ys | (zs ** prf) | (No contra)
        = (x :: zs ** Neg contra prf)

namespace DList
  public export
  map : (f  : forall x . this x -> that x)
     -> (ts : DList ty this xs)
           -> DList ty that xs
  map f [] = []
  map f (elem :: rest)
    = f elem :: map f rest

  public export
  data Union : (xs : DList a p ps)
            -> (ys : DList a p ps')
            -> (zs : DList a p ps'')
            -> (prf : Union ps ps' ps'') -> Type
    where
      End : Union Nil ys ys End
      Pos : {xs : DList a p ps}
         -> {ys : DList a p ps'}
         -> Union     xs  ys zs            rest
         -> Union (x::xs) ys zs (Pos prf' rest)
      Neg : {xs : DList a p ps}
         -> {ys : DList a p ps'}
         -> Union     xs  ys     zs            rest
         -> Union (x::xs) ys (x::zs) (Neg prf' rest)


  union' : (xs  : DList a p ps)
        -> (ys  : DList a p ps')
        -> (prf : Union ps ps' ps'')
               -> (zs : DList a p ps'' ** Union xs ys zs prf)
  union' [] ys End
    = (ys ** End)

  union' (elem :: rest) ys (Pos x y) with (union' rest ys y)
    union' (elem :: rest) ys (Pos x y) | (zs ** prf)
      = (zs ** Pos prf)

  union' (elem :: rest) ys (Neg f x) with (union' rest ys x)
    union' (elem :: rest) ys (Neg f x) | (zs ** prf)
      = (elem :: zs ** Neg prf)

  export
  union : DecEq a
       => {ps, ps' : _}
       -> (xs  : DList a p ps)
       -> (ys  : DList a p ps')
              -> (ps'' : List a ** zs : DList a p ps''     **
                  prf : Union ps ps' ps'' ** Union xs ys zs prf)
  union {ps} {ps'} xs ys with (Bootstrap.List.union ps ps')
    union {ps = ps} {ps' = ps'} xs ys | (zs ** prf) with (union' xs ys prf)
      union {ps = ps} {ps' = ps'} xs ys | (zs ** prf) | (rest ** prf') = (zs ** rest ** prf ** prf')


namespace Context
  export
  keys : Context ty xs
      -> List String
  keys [] = []
  keys ((I name x) :: rest) = name :: keys rest


-- [ EOF ]
