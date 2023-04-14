|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Capable.Types.Protocol.Unification

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


import Capable.Bootstrap
import Capable.Error
import Capable.Types.Role
import Capable.Types.Base

import Capable.Types.Protocol.Local
import Capable.Types.Protocol.Local.Synth
import Capable.Types.Protocol.Selection

%default total

mutual
  namespace Branch
    public export
    data Unify : (this : Branch Local.Local ks rs x)
              -> (that : Branch Synth.Local ks rs y)
                      -> Type
      where
        B : Unify this that
         -> Unify (B l t this)
                  (B l t that)

  namespace Branches

    public export
    data Unify : (this : Local.Branches ks rs las)
              -> (that : Synth.Branches ks rs lbs)
                      -> Type
      where
        Nil : Unify Nil Nil
        (::) : Unify this  that
            -> Branches.Unify these those
            -> Unify (this::these)
                     (that::those)

  namespace Protocol
    public export
    data Unify : (this : Local.Local ks rs)
              -> (that : Synth.Local ks rs)
                      -> Type

      where
        Crash : Unify Crash Crash
        End : Unify End End
        Call : Unify (Call idx) (Call idx)
        Rec  : Unify this that
            -> Unify (Rec this) (Rec that)

        Select : {this : _}
              -> Select (B l tyM this) (F l prfM) (o::os) (p::ps)
              -> Protocol.Unify this that
              -> Unify (Choice SELECT target (Val (UNION (f:::fs))) (UNION (p::ps)) (o::os))
                       (Select        target l tyM prfM that)

        Choice : Unify these those
              -> Unify (Choice BRANCH target ty prfOS these)
                       (Offer         target ty prfOS those)

Uninhabited (Unify Crash End) where
  uninhabited _ impossible

Uninhabited (Unify Crash (Call q)) where
  uninhabited _ impossible

Uninhabited (Unify Crash (Rec q)) where
  uninhabited _ impossible

Uninhabited (Unify Crash (Select a b c d e)) where
  uninhabited _ impossible

Uninhabited (Unify Crash (Offer a b c d)) where
  uninhabited _ impossible

Uninhabited (Unify End (Call q)) where
  uninhabited _ impossible

Uninhabited (Unify End (Rec q)) where
  uninhabited _ impossible

Uninhabited (Unify End (Select a b c d e)) where
  uninhabited _ impossible

Uninhabited (Unify End (Offer a b c d)) where
  uninhabited _ impossible

Uninhabited (Unify (Call idx) (Rec q)) where
  uninhabited _ impossible

Uninhabited (Unify (Call idx) (Select a b c d e)) where
  uninhabited _ impossible

Uninhabited (Unify (Call idx) (Offer a b c d)) where
  uninhabited _ impossible

Uninhabited (Unify (Rec idx) (Select a b c d e)) where
  uninhabited _ impossible

Uninhabited (Unify (Choice q w x y z) Crash) where
  uninhabited _ impossible

Uninhabited (Unify (Choice q w x y z) (Rec a)) where
  uninhabited _ impossible

Uninhabited (Unify (Choice q w x y z) (Call a)) where
  uninhabited _ impossible

Uninhabited (Unify (Choice q w x y z) (End)) where
  uninhabited _ impossible

Uninhabited (Unify (Choice BRANCH w x y z) (Select a b c d e)) where
  uninhabited _ impossible

Uninhabited (Unify (Choice SELECT w x y z) (Offer a b c d)) where
  uninhabited _ impossible

Uninhabited (Unify Nil (x::xs)) where
  uninhabited [] impossible
  uninhabited (y :: z) impossible

Uninhabited (Unify (x::xs) Nil) where
  uninhabited [] impossible
  uninhabited (y :: z) impossible

Uninhabited (Unify End Crash) where
  uninhabited _ impossible

Uninhabited (Unify (Call x) Crash) where
  uninhabited _ impossible

Uninhabited (Unify (Call x) End) where
  uninhabited _ impossible

Uninhabited (Unify (Rec x) End) where
  uninhabited _ impossible

Uninhabited (Unify (Rec x) Crash) where
  uninhabited _ impossible

Uninhabited (Unify (Rec x) (Call a)) where
  uninhabited _ impossible


Uninhabited (Unify (Rec x) (Offer whom typ prfM ca)) where
  uninhabited _ impossible

{- @TODO Revisit
mutual
  namespace Branch
    export
    unify : (this : Branch Local.Local ks rs x)
         -> (that : Branch Synth.Local ks rs y)
                 -> DecInfo ()
                            (Unify this that)
    unify (B l b k) (B a q c) with (decEq l a)
      unify (B l b k) (B l q c) | (Yes Refl) with (decEq b q)
        unify (B l b k) (B l b c) | (Yes Refl) | (Yes Refl) with (unify k c)
          unify (B l b k) (B l b c) | (Yes Refl) | (Yes Refl) | (Yes p)
            = Yes (B p)
          unify (B l b k) (B l b c) | (Yes Refl) | (Yes Refl) | (No msg no)
            = No ()
                 (\case (B z) => no z)

        unify (B l b k) (B l q c) | (Yes Refl) | (No contra)
          = No ()
               (\case (B z) => contra Refl)
      unify (B l b k) (B a q c) | (No contra)
        = No ()
             (\case (B z) => contra Refl)

  namespace Branches


    export
    unify : (this : Local.Branches ks rs las)
         -> (that : Synth.Branches ks rs lbs)
                 -> DecInfo ()
                            (Unify this that)
    unify [] []
      = Yes []

    unify [] (elem :: rest)
      = No ()
           absurd
    unify (elem :: rest) []
      = No ()
           absurd
    unify (x :: xs) (y :: ys) with (unify x y)
      unify (x :: xs) (y :: ys) | (Yes prf) with (unify xs ys)
        unify (x :: xs) (y :: ys) | (Yes prf) | (Yes prfs)
          = Yes (prf :: prfs)
        unify (x :: xs) (y :: ys) | (Yes prf) | (No msg no)
          = No ()
               (\case (z :: w) => no w)

      unify (x :: xs) (y :: ys) | (No msg no)
        = No ()
             (\case (z :: w) => no z)

  namespace Protocol

    export
    unify : (this : Local.Local ks rs)
         -> (that : Synth.Local ks rs)
                 -> DecInfo ()
                            (Unify this that)
    unify Crash Crash = Yes Crash
    unify Crash End                               = No () absurd
    unify Crash (Call x)                          = No () absurd
    unify Crash (Rec x)                           = No () absurd
    unify Crash (Select whom label type prf cont) = No () absurd
    unify Crash (Offer whom type prfM choices)    = No () absurd

    unify End Crash = No () absurd
    unify End End = Yes End
    unify End (Call x)                          = No () absurd
    unify End (Rec x)                           = No () absurd
    unify End (Select whom label type prf cont) = No () absurd
    unify End (Offer whom type prfM choices)    = No () absurd

    unify (Call x) Crash = No () absurd
    unify (Call x) End   = No () absurd
    unify (Call x) (Call y) with (Index.decEq x y)
      unify (Call x) (Call x) | (Yes (Same Refl Refl))
        = Yes Call
      unify (Call x) (Call y) | (No contra)
        = No ()
             (\case Call => contra (Same Refl Refl))

    unify (Call x) (Rec y)                           = No () absurd
    unify (Call x) (Select whom label type prf cont) = No () absurd
    unify (Call x) (Offer whom type prfM choices)    = No () absurd

    unify (Rec x) Crash    = No () absurd
    unify (Rec x) End      = No () absurd
    unify (Rec x) (Call y) = No () absurd
    unify (Rec x) (Rec y)  with (unify x y)
      unify (Rec x) (Rec y)  | (Yes prfWhy)
        = Yes (Rec prfWhy)
      unify (Rec x) (Rec y)  | (No msg no)
        = No ()
             (\case (Rec z) => no z)

    unify (Rec x) (Select whom label type prf cont)
      = No () absurd
    unify (Rec x) (Offer whom type prfM choices)
      = No () absurd
    unify (Choice kind whom type prfM choices) Crash    = No () absurd
    unify (Choice kind whom type prfM choices) End      = No () absurd
    unify (Choice kind whom type prfM choices) (Call x) = No () absurd
    unify (Choice kind whom type prfM choices) (Rec x)  = No () absurd

    unify (Choice SELECT whom (Val (UNION (f:::fs))) (UNION prfM) choices) (Select x label y prf cont)
      = case Index.decEq whom x of
          No no => No () (\case (Select a v) => no (Same Refl Refl))
          Yes (Same Refl Refl)
            => case select label prfM choices of
                 (No contra) => No () (\case (Select z w) => contra (R y _ (F label prf) z))
                 (Yes (R t c z w))
                   => case unify c cont of
                           (No msg no) => No () (\case (Select v s) => no ?ass)
                           (Yes prfWhy) => ?a_0



    unify (Choice BRANCH whom type prfM choices) (Select x label y prf cont)
      = No () absurd

    unify (Choice BRANCH whom (Val (UNION (x:::xs))) prfM choices) (Offer w (Val (UNION (y:::ys))) z c)
      = case Index.decEq whom w of
          No no => No () (\case (Choice v) => no (Same Refl Refl))
          Yes (Same Refl Refl)
            => case decEq (UNION (x:::xs)) (UNION (y:::ys)) of
                 No no => No () (\case (Choice v) => no Refl)
                 Yes Refl
                   => case Marshall.decEq prfM z Refl of
                       Refl
                         => case unify choices c of
                              No msg no => No () (\case (Choice v) => no v)
                              Yes prf => Yes (Choice prf)
    unify (Choice SELECT whom type prfM choices) (Offer x y z w)
      = No () absurd

-}
-- [ EOF ]
