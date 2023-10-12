module Capable.Bootstrap

import Control.WellFounded
import Data.Nat

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
vect : List (Doc ann) -> Doc ann
vect = group . encloseSep (flatAlt (pretty "< ") (pretty "<"))
                          (flatAlt (pretty " >") (pretty ">"))
                          (pretty ", ")

export
reflect : (ctxt  : Context a rs)
       -> (loc   : IsVar rs l)
                -> String
reflect [] (V _ Here) impossible
reflect [] (V _ (There later)) impossible

reflect ((I name x) :: rest) (V 0 prf) = name
reflect (elem :: rest) (V (S k) (There later)) = reflect rest (V k later)

export
rebuild : (a -> String)
       -> (as : List a)
              -> Context a as
rebuild _ [] = []
rebuild f (x :: xs) = I (f x) x :: rebuild f xs

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

namespace DList
  public export
  data IsSucc : (xs : DList idx ty is) -> Type where
    ItIsSucc : IsSucc (x::xs)


  isEmpty : {xs : DList idx ty Nil} -> IsSucc xs -> Void
  isEmpty ItIsSucc impossible

  export
  isSucc : (xs : DList idx ty is) -> Dec (IsSucc xs)
  isSucc []
    = No isEmpty
  isSucc (_ :: _)
    = Yes ItIsSucc

  public export
  (++) : DList i e xs
      -> DList i e ys -> DList i e (xs ++ ys)
  (++) Nil ys = ys
  (++) (x::xs) ys = x :: append xs ys

  public export
  data Split : (0 idx : Type)
            -> (0 ty  : idx -> Type)
            -> {0 is  : List idx}
            -> (  xs  : DList idx ty is) -> Type where
    SNil : Split idx e Nil
    SOne : (x : e i) -> Split idx e [x]
    SPair : (x : e i) -> (xs : DList idx e is)
         -> (y : e j) -> (ys : DList idx e js)
         -> Split idx e ((x::xs) ++ (y::ys))

  splitHelp : (h : e i)
           -> (t : DList idx e is)
           -> (c : DList idx e js)
                -> Split idx e (h::t)
  splitHelp h [] c
    = SOne h

  splitHelp h (x :: xs) []
    = SPair h Nil x xs

  splitHelp h (x :: xs) [y]
    = SPair h Nil x xs

  splitHelp h (x :: xs) (_ :: _ :: ys)
    = case splitHelp h xs ys of
        (SOne h) => SPair h [] _ []
        (SPair h' xs y' ys) => SPair h' (x::xs) y' ys

  -- linear
  export
  split : (xs : DList idx e is) -> Split idx e xs
  split []
    = SNil
  split (x :: xs) = splitHelp x xs xs


  public export
  data SplitRec : (0 idx : Type)
               -> (0 e   : idx -> Type)
               -> {0 is  : List idx}
               -> (  xs  : DList idx e is)
                        -> Type
    where
      SNilRec : SplitRec idx e Nil
      SOneRec : (x : e i) -> SplitRec idx e [x]
      SPairRec : (ls : DList idx e is)
              -> (rs : DList idx e js)
              -> (lr : Lazy (SplitRec idx e ls))
              -> (rr : Lazy (SplitRec idx e rs))
                    -> SplitRec idx e (ls ++ rs)

  public export
  Sized (DList idx e is) where
    size = DList.size

--  public export
--  splitRec : (xs : DList idx e is) -> SplitRec idx e xs
--  splitRec xs with (sizeAccessible xs)
--    splitRec xs | acc  with (split xs)
--      splitRec [] | acc  | SNil = ?splitRec_rhs_rhs_rhs_0
--      splitRec [x] | acc  | (SOne x) = ?splitRec_rhs_rhs_rhs_1
--      splitRec ((x :: y) ++ (z :: ys)) | acc  | (SPair x y z ys) = ?splitRec_rhs_rhs_rhs_2


namespace DList.All.Informative

  export
  all : {0 p : {i : kind} -> (x : type i) -> Type}
     -> (  f : {i : kind} -> (x : type i) -> DecInfo e (p x))
     -> ( xs : DList kind type is)
            -> DecInfo e (All kind type p is xs)
  all f []
    = Yes []
  all f (elem :: rest) with (f elem)
    all f (elem :: rest) | (Yes prf) with (all f rest)
      all f (elem :: rest) | (Yes prf) | (Yes prfs)
        = Yes (prf :: prfs)

      all f (elem :: rest) | (Yes prf) | (No msg no)
        = No msg (\case (x :: later) => no later)

    all f (elem :: rest) | (No msg no)
      = No msg (\case (x::later) => no x)

-- [ EOF ]
