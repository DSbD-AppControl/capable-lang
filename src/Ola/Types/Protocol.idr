|||
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
module Ola.Types.Protocol

import Decidable.Equality
import Data.String

import public Data.Singleton

import Data.List.Elem
import Data.List1
import Data.List.Quantifiers

import Toolkit.Decidable.Do
import public Toolkit.Decidable.Informative
import public Toolkit.Decidable.Equality.Indexed

import Toolkit.Data.List.Quantifiers

import public Toolkit.Data.DList
import Toolkit.Data.DList.All

import public Toolkit.DeBruijn.Renaming


import Ola.Bootstrap
import Ola.Types.Role
import Ola.Types.Base

%default total

public export
data Kind = R -- To capture recursion variables

export
DecEq Kind where
  decEq R R = Yes Refl

public export
data Branch : (0 contType : List Kind -> List Role -> Type)
           -> (  ks       : List Kind)
           -> (  rs       : List Role)
           -> (  f        : (String, Base))
                         -> Type
  where
    B : {0 contType : List Kind -> List Role -> Type}
     -> (l : String)
     -> (b : Base)
     -> (cont : contType ks rs)
             -> Branch contType ks rs (l,b)

namespace Global

  public export
  data Global : List Kind -> List Role -> Type where
    End : Global ks rs

    Call : IsVar vs R -> Global vs rs

    Rec : Global (R::vs) rs
       -> Global     vs  rs

    Choice : (s : IsVar rs MkRole)
          -> (r : IsVar rs MkRole)
          -> (type   : Singleton (UNION (field:::fields)))
          -> (prfR   : Not (Equals Role (IsVar rs) s r))
          -> (opties : DList (String,Base)
                             (Branch Global ks rs)
                             (field::fields))
                    -> Global vs rs

namespace Local


  public export
  data ChoiceTy = BRANCH | SELECT

  notBS : BRANCH = SELECT -> Void
  notBS Refl impossible

  export
  DecEq ChoiceTy where
    decEq BRANCH BRANCH = Yes Refl
    decEq BRANCH SELECT = No notBS
    decEq SELECT BRANCH = No (negEqSym notBS)
    decEq SELECT SELECT = Yes Refl


  public export
  data Local : List Kind -> List Role -> Type where
    End : Local ks rs
    Call : {vs : _} -> IsVar vs R -> Local vs rs
    Rec : Local (R::vs) rs -> Local vs rs
    Choice : (kind : ChoiceTy)
          -> (whom : IsVar rs MkRole)
          -> (type : Singleton (UNION (field:::fields)))
          -> (choices : DList (String,Base)
                              (Branch Local ks rs)
                              (field::fields))
                     -> Local ks rs

  Uninhabited (Local.End = (Local.Call x)) where
    uninhabited Refl impossible

  Uninhabited (Local.End = (Local.Rec x)) where
    uninhabited Refl impossible

  Uninhabited (Local.End = (Local.Choice a b c d)) where
    uninhabited Refl impossible

  Uninhabited (Local.Call x = (Local.Rec y)) where
    uninhabited Refl impossible

  Uninhabited (Local.Call x = (Local.Choice a b c d)) where
    uninhabited Refl impossible

  Uninhabited (Local.Rec x = (Local.Choice a b c d)) where
    uninhabited Refl impossible



  mutual
    namespace Branch
      export
      decEq : (a : Branch Local ks rs (f,s))
           -> (b : Branch Local ks rs (x,y))
                -> Dec (Equal a b)
      decEq (B f s contA) (B x y contB)
        = decDo $ do Refl <- decEq f x `otherwise` (\Refl => Refl)
                     Refl <- decEq s y `otherwise` (\Refl => Refl)
                     Refl <- Local.decEq contA contB `otherwise` (\Refl => Refl)
                     pure Refl

    namespace Branches
      export
      decEq : (as : DList (String,Base)
                          (Branch Local ks rs)
                          (fs))
           -> (bs : DList (String,Base)
                          (Branch Local ks rs)
                          (gs))
                -> Dec (Equal as bs)
      decEq as bs with (shape as bs)
        decEq [] [] | Empty = Yes Refl
        decEq (x :: xs) [] | LH = No isLeftHeavy
        decEq [] (x :: xs) | RH = No isRightHeavy
        decEq (B xl xt cx :: xs) (B yl yt cy :: ys) | Same
          = decDo $ do Refl <- Branch.decEq (B xl xt cx) (B yl yt cy)
                                 `otherwise` (\Refl => Refl)
                       Refl <- Branches.decEq xs ys `otherwise` (\Refl => Refl)
                       pure Refl

    public export
    decEq : (a,b : Local ks rs) -> Dec (Equal a b)
    decEq End End
      = Yes Refl
    decEq End (Call x)
      = No absurd
    decEq End (Rec x)
      = No absurd
    decEq End (Choice kind whom t choices)
      = No absurd

    decEq (Call x) End
      = No (negEqSym absurd)

    decEq (Call x) (Call y)
      = case Index.decEq x y of
             No no => No (\Refl => no (Same Refl Refl))
             Yes (Same Refl Refl) => Yes Refl

    decEq (Call x) (Rec y)
      = No absurd
    decEq (Call x) (Choice kind whom t choices)
      = No absurd

    decEq (Rec x) End
      = No (negEqSym absurd)
    decEq (Rec x) (Call y)
      = No (negEqSym absurd)

    decEq (Rec x) (Rec y) with (Local.decEq x y)
      decEq (Rec x) (Rec x) | (Yes Refl)
        = Yes Refl
      decEq (Rec x) (Rec y) | (No contra)
        = No (\Refl => contra Refl)

    decEq (Rec x) (Choice kind whom t choices) = No absurd

    decEq (Choice kind whom t choices) End
      = No (negEqSym absurd)
    decEq (Choice kind whom t choices) (Call x)
      = No (negEqSym absurd)
    decEq (Choice kind whom t choices) (Rec x)
      = No (negEqSym absurd)
    decEq (Choice a b (Val (UNION (f:::fs))) cs) (Choice x y (Val (UNION (g:::gs))) zs)
      = decDo $ do Refl <- decEq a x `otherwise` (\Refl => Refl)
                   Refl <- decEq b y `otherwise` (\Refl => Refl)
                   Refl <- decEq (UNION (f:::fs)) (UNION (g:::gs)) `otherwise` (\Refl => Refl)
                   Refl <- Branches.decEq cs zs `otherwise` (\Refl => Refl)
                   pure Refl

    public export
    DecEq (Local ks rs) where
      decEq = Local.decEq


    export
    branchesEq : (b  : Branch Local ks rs (l,t))
              -> (bs : DList (String, Base)
                             (Branch Local ks rs)
                             ls)
                    -> DecInfo ()
                               (All (String,Base)
                                    (Branch Local ks rs)
                                    (Equal b)
                                    ls
                                    bs)
    branchesEq b []
      = Yes []
    branchesEq b ((B str x cont) :: rest) with (Branch.decEq b (B str x cont))
      branchesEq b ((B str x cont) :: rest) | (Yes prf) with (branchesEq b rest)
        branchesEq b ((B str x cont) :: rest) | (Yes prf) | (Yes prfWhy)
          = Yes (prf :: prfWhy)
        branchesEq b ((B str x cont) :: rest) | (Yes prf) | (No _ no)
          = No () (\(h::t) => no t)

      branchesEq b ((B str x cont) :: rest) | (No no)
        = No () (\(h::t) => no h)

namespace Global
  public export
  Branches : List Kind -> List Role -> List (String, Base) -> Type
  Branches ks rs
    = DList (String, Base)
            (Branch Global ks rs)

namespace Local

  public export
  Branches : List Kind -> List Role -> List (String, Base)-> Type
  Branches ks rs
    = DList (String, Base)
            (Branch Local ks rs)

-- [ EOF ]
