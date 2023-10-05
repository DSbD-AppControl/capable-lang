|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Capable.Types.Protocol.Subset

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
import Toolkit.Data.DList.Any

import public Toolkit.DeBruijn.Renaming

import Capable.Bootstrap
import Capable.Error
import Capable.Types.Role
import Capable.Types.Base

import Capable.Types.Protocol.Local
import Capable.Types.Protocol.Selection

%default total


namespace Branch
  public export
  data Subset : (ks : List Kind)
             -> (rs : List Role)
             -> (0 s : (x : Local ks rs)
                    -> (y : Local ks rs) -> Type)
             -> (this : Branch Local.Local ks rs x)
             -> (that : Branch Local.Local ks rs y)
                     -> Type
    where
      B : (pL : Equal la lb)
       -> (pT : Equal ta tb)
       -> (pS : s this that)
       -> Subset ks rs s
                 (B la ta this)
                 (B lb tb that)

  export
  subset : (f : (x,y : Local ks rs) -> DecInfo () (s x y))
        -> (x : Branch Local.Local ks rs lx)
        -> (y : Branch Local.Local ks rs ly)
             -> DecInfo ()
                        (Subset ks rs s x y)
  subset f (B lx tx cx) (B ly ty cy)
    = case decEq lx ly of
        No no
          => No () (\(B Refl _ _) => no Refl)

        Yes Refl
          => case decEq tx ty of
               No no
                 => No () (\(B _ Refl _) => no Refl)
               Yes Refl
                 => case f cx cy of
                      No msg no
                        => No () (\(B _ _ prf) => no prf)
                      Yes prf
                        => Yes (B Refl Refl prf)
namespace Exists
  public export
  Subset : {lbs : _}
        -> {ks : List Kind}
             -> {rs : List Role}
             -> (0 s : (x : Local ks rs)
                    -> (y : Local ks rs) -> Type)
             -> (this  : Branch Local.Local ks rs x)
             -> (those : Local.Branches ks rs lbs)
                      -> Type
  Subset s this those
    = Any (String,Base)
          (Branch Local.Local ks rs)
          (Subset ks rs s this)
          those

  export
  subset : {ks, rs : _}
        -> {0 s : (x,y : Local ks rs) -> Type}
        -> (f : (x,y : Local ks rs) -> DecInfo () (s x y))
        -> (x  : Branch Local.Local ks rs lx)
        -> (ys : Local.Branches ks rs lys)
               -> DecInfo ()
                          (Subset s x ys)
  subset f x ys
    = case DList.Any.any (subset f x) ys of
        No no => No () (\prf => no prf)
        Yes prf => Yes prf

namespace Offer
  {- [ NOTE ] should be all but comes out as not being strictley positive. -}

  public export
  data Subset : (ks : List Kind)
             -> (rs : List Role)
             -> (0 s : (x : Local ks rs)
                    -> (y : Local ks rs) -> Type)
             -> (these : Local.Branches ks rs las)
             -> (those : Local.Branches ks rs lbs)
                      -> Type
    where
      Empty : Offer.Subset ks rs s Nil Nil
      Next : Subset ks rs s this that
          -> Offer.Subset ks rs s these those
          -> Offer.Subset ks rs s (this::these) (that::those)

  Uninhabited (Subset ks rs s Nil (x::xs))
    where
      uninhabited _ impossible

  Uninhabited (Subset ks rs s (x::xs) Nil)
    where uninhabited _ impossible

  export
  subset : {0 s : (x,y : Local ks rs) -> Type}
        -> (f : (x,y : Local ks rs) -> DecInfo () (s x y))
        -> (xs : Local.Branches ks rs lxs)
        -> (ys : Local.Branches ks rs lys)
               -> DecInfo ()
                          (Offer.Subset ks rs s xs ys)
  subset f xs ys with (shape xs ys)
    subset f [] [] | Empty
      = Yes Empty

    subset f (x :: xs) [] | LH = No () absurd
    subset f [] (x :: xs) | RH = No () absurd

    subset f (x :: xs) (y :: ys) | Same
      = case subset f x y of
         No msg no => No () (\(Next px _) => no px)
         Yes px
           => case subset f xs ys of
                No msg no => No () (\(Next _ pxs) => no pxs)
                Yes pxs => Yes (Next px pxs)

namespace Select
  {- [ NOTE ] should be all but comes out as not being strictley positive. -}

  public export
  data Subset : (ks : List Kind)
             -> (rs : List Role)
             -> (0 s : (x : Local ks rs)
                    -> (y : Local ks rs) -> Type)
             -> (these : Local.Branches ks rs las)
             -> (those : Local.Branches ks rs lbs)
                      -> Type
    where
      Empty : Select.Subset ks rs s Nil those
      Next : Exists.Subset s this those
          -> Select.Subset ks rs s these those
          -> Select.Subset ks rs s (this::these) those

  export
  subset : {ks,rs : _}
        -> {0 s : (x,y : Local ks rs) -> Type}
        -> (f : (x,y : Local ks rs) -> DecInfo () (s x y))
        -> (xs : Local.Branches ks rs lxs)
        -> (ys : Local.Branches ks rs lys)
               -> DecInfo ()
                          (Select.Subset ks rs s xs ys)
  subset f [] ys
    = Yes Empty

  subset f (x :: xs) ys with (subset f x ys)
    subset f (x :: xs) ys | (Yes pfX) with (Select.subset f xs ys)
      subset f (x :: xs) ys | (Yes pfX) | (Yes pfXS)
        = Yes (Next pfX pfXS)

      subset f (x :: xs) ys | (Yes pfX) | (No pfXS no)
        = No ()
             (\(Next _ pxs) => no pxs)

    subset f (x :: xs) ys | (No msg no)
      = No ()
           (\(Next px _) => no px)


namespace Protocol
  public export
  data Subset : (this : Local.Local ks rs)
             -> (that : Local.Local ks rs)
                    -> Type

    where
      Crash : Subset Crash Crash

      End : Subset End End

      Call : Subset (Call idx) (Call idx)

      Rec  : Subset this that
          -> Subset (Rec k this) (Rec k that)

      Offer : Offer.Subset ks rs Protocol.Subset these those
           -> Subset (ChoiceL BRANCH target tyA prfA these)
                     (ChoiceL BRANCH target tyB prfB those)

      Select : Select.Subset ks rs Protocol.Subset these those
            -> Subset (ChoiceL SELECT target tyA prfA these)
                      (ChoiceL SELECT target tyB prfB those)

  export
  subset : {ks,rs : _}
        -> (x,y : Local.Local ks rs)
               -> DecInfo () (Subset x y)
  subset x y with (sameShapedHead x y)
    subset x y | (Yes (SS shape)) with (shape)
      subset Crash Crash | (Yes (SS shape)) | Crash
        = Yes Crash

      subset End End | (Yes (SS shape)) | End
        = Yes End

      subset (Call prfA) (Call prfB) | (Yes (SS shape)) | Call
        = case Index.decEq prfA prfB of
            No no => No ()
                        (\Call => no (Same Refl Refl))
            Yes (Same Refl Refl)
              => Yes Call

      subset (Rec a kA) (Rec b kB) | (Yes (SS shape)) | Rec
        = case decEq a b of
            (No no)
              => No ()
                    (\(Rec ltr) => no Refl)
            (Yes Refl)
              => case subset kA kB of
                   (Yes prf)
                     => Yes (Rec prf)
                   (No msg no)
                     => No ()
                           (\(Rec prf) => no prf)


      subset (ChoiceL BRANCH wB tyA prfA cbs)
             (ChoiceL BRANCH wA tyB prfB cas) | (Yes (SS shape)) | Offer
        = case Index.decEq wB wA of
            No no
              => No ()
                    (\(Offer _) => no (Same Refl Refl))
            Yes (Same Refl Refl)
              => case assert_total $ Offer.subset Protocol.subset cbs cas of
                   No msg no
                     => No ()
                           (\(Offer prf) => no prf)

                   Yes prf
                     => Yes (Offer prf)



      subset (ChoiceL SELECT wB typeB prfB cbs)
             (ChoiceL SELECT wA typeA prfA cas) | (Yes (SS shape)) | Select
        = case Index.decEq wB wA of
            No no
              => No ()
                    (\(Select _) => no (Same Refl Refl))
            Yes (Same Refl Refl)
              => case assert_total $ Select.subset Protocol.subset cbs cas of
                   No msg no
                     => No ()
                           (\(Select prf) => no prf)

                   Yes prf
                     => Yes (Select prf)


    subset x y | (No contra)
      = No ()
           (\pf => diffHeads contra pf)

      where
        diffHeads : {this,that : _}
                 -> (SameShapedHead this that -> Void)
                 -> (Subset this that)
                 -> Void
        diffHeads f q with (q)
          diffHeads f q | Crash = f (SS Crash)
          diffHeads f q | End = f (SS End)
          diffHeads f q | Call = f (SS Call)
          diffHeads f q | (Rec z) = f (SS Rec)
          diffHeads f q | (Offer z) = f (SS Offer)
          diffHeads f q | (Select z) = f (SS Select)


namespace Cases
  public export
  Subset : {lbs : _}
        -> {ks : List Kind}
             -> {rs : List Role}
             -> (these : Local.Branches ks rs lbs)
             -> (that  : Local.Local ks rs)
                      -> Type
  Subset these that
    = DList.All.All (String,Base)
                    (Branch Local.Local ks rs)
                    (\(B l t c) => Subset c that)
                    lbs
                    these

  export
  subset : {ks, rs : _}
        -> (ys : Local.Branches ks rs lys)
        -> (x  : Local.Local ks rs)
               -> DecInfo ()
                          (Cases.Subset ys x)
  subset ys x
    = case DList.All.Informative.all (\(B _ _ y) => Protocol.subset y x) ys of
        No () no => No () (\prf => no prf)
        Yes prf => Yes prf

-- [ EOF ]
