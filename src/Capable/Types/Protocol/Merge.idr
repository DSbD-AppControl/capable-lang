||| Full Merging Local types for synthesis.
|||
||| Standard merge semantics has been defined for projection, which we will refer to as /Full Projection Merge/.
||| We are instead interested in /merging for synthesis/, or /Full Synthesis Merge/.
|||
||| /Full Synthesis Merge/ differs from /Full Projection Merge/ only in how selection and offering are treated.
||| We, simply, swap the semantics.
||| That is, for Full Synthesis Merge we require merging of Offers to be exact, and Selection to be greatest covering.
|||
||| Offers in Capable are analgous to case-spliting (pattern matching) but with fixed top-level patterns that _must_ be covering.
||| Thus their merging must too be covering and exact in all instances that an offer is seen.
|||
||| Selection, on the otherhand, is a process of limited discovery.
||| When merging selections we are merging only what we see, and the merge semantics must reflect that.
||| When merging selections we start with the set differences (based on their labels) and then merge their intersections.
||| Such a semantics provides us with the greatest level of limit discovery we can do.
|||
||| @TODO This module should probably be renamespaced later as `Merge.Synthesis.Full`, with the plain merge used in projection similarly incorporated.
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Capable.Types.Protocol.Merge

import Decidable.Equality
import Data.String

import public Data.Singleton

import Data.List.Elem
import Data.List1
import Data.List.Quantifiers

import Data.Void

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
import Capable.Types.Protocol.Selection

%default total

||| How do branches meet during intersection.
|||
||| Meet is a view on the results of merging two branches x and y, such that we require the result of the meeting at the type-level.
||| Definition
|||
||| Lemma X will ‘Meet’ Y if labels and types match, and continuations can merge.
|||
||| Meeting either:
|||
||| YM
|||     Successful and will produce a new branch.
||| NM
|||     X does not meeting with Y, think sharks and jets ;-)
||| FMT
|||     Although X should meet with Y the types themselves do not meet.
||| FMM
|||     Although X should meet with Y, and the types meet, merging fails.
|||
namespace Meet

  public export
  data Result : (ks : List Kind)
             -> (rs : List Role)
                   -> Type
    where
      YesMeet : {ltc : _}
             -> (pM  : Marshable ltc)
             -> (nB  : Branch Local ks rs ltc)
                    -> Result ks rs

      NoMeet : Result ks rs
      Fail : Result ks rs

  public export
  data Meet : (ks : List Kind)
           -> (rs : List Role)
           -> (0 p : (x : Local ks rs)
                  -> (y : Local ks rs)
                  -> (z : Local ks rs)
                       -> Type)
           -> (mx : Marshable lx)
           -> (x  : Branch Local ks rs lx)
           -> (my : Marshable ly)
           -> (y  : Branch Local ks rs ly)
                -> Result ks rs
                -> Type
    where
      Y : (pL : Equal la lb)
       -> (pT : Equal ta tb)
       -> (pM : p    ca cb cc)
             -> Meet ks rs p (F la px) (B la ta ca)
                             (F lb py) (B lb tb cb)
                             (YesMeet (F la px) (B la ta cc))
      N : (pL : Equal la lb -> Void)
             -> Meet ks rs p (F la px) (B la ta ca)
                             (F lb py) (B lb tb cb)
                             NoMeet

      FT : (pL : Equal la lb)
        -> (pT : Equal ta tb -> Void)
              -> Meet ks rs p (F la px) (B la ta ca)
                              (F lb py) (B lb tb cb)
                              Fail

      FM : (pL : Equal la lb)
        -> (pT : Equal ta tb)
        -> (pM : {cc : _} -> p ca cb cc -> Void)
              -> Meet ks rs p (F la px) (B la ta ca)
                              (F lb py) (B lb tb cb)
                              Fail


  export
  meet : (f : (x : Local ks rs)
           -> (y : Local ks rs)
                -> DecInfo () (DPair (Local ks rs) (p x y)))

      -> (px : Marshable lx) -> (x : Branch Local ks rs lx)
      -> (py : Marshable ly) -> (y : Branch Local ks rs ly)
            -> DPair (Result ks rs)
                     (Meet ks rs p px x py y)

  meet f (F lx px) (B lx tx cx) (F ly py) (B ly ty cy)
    = case decEq lx ly of
        (Yes Refl)
          => case decEq tx ty of
               (Yes Refl)
                 => case f cx cy of
                      (Yes (cz ** prf))
                        => (YesMeet (F ly px) (B ly ty cz) ** Y Refl Refl prf)

                      (No msg no)
                        => (Fail ** FM Refl Refl (\x => no (_ ** x)))

               (No no)
                 => (Fail ** FT Refl no)

        (No no)
          => (NoMeet ** N no)

||| Meets is a proposition that only records no meets and successful
||| meets only.
|||
||| A valid meet between X and YS is one in which there are only no
||| meetings or successful ones. The result will be a potentially
||| empty list of the successful meetings.
|||
namespace Meets
  public export
  data Meets : (ks : List Kind)
            -> (rs : List Role)
            -> (0 p : (x : Local ks rs)
                   -> (y : Local ks rs)
                   -> (z : Local ks rs)
                        -> Type)
            -> (px : Marshable lx)
            -> (x  : Branch Local ks rs lx)
            -> (py : DList (String,Base) Marshable lys)
            -> (ys : Local.Branches ks rs lys)
            -> (pz : DList (String,Base) Marshable lzs)
            -> (zs : Local.Branches ks rs lzs)
                  -> Type
    where
      Empty : Meets ks rs p px x Nil Nil Nil Nil

      MeetXY : Meet  ks rs p px x  py        y      (YesMeet pz        z)
            -> Meets ks rs p px x      pys      ys               pzs      zs
            -> Meets ks rs p px x (py::pys) (y::ys)         (pz::pzs) (z::zs)

      MeetNo : Meet  ks rs p px x py         y         NoMeet
            -> Meets ks rs p px x      pys      ys  pzs zs
            -> Meets ks rs p px x (py::pys) (y::ys) pzs zs

  public export
  data MeetsResult : (ks : List Kind)
                  -> (rs : List Role)
                  -> (0 p : (x : Local ks rs)
                         -> (y : Local ks rs)
                         -> (z : Local ks rs)
                              -> Type)

                  -> (px  : Marshable lx)
                  -> (x   : Branch Local ks rs lx)
                  -> (pys : DList (String,Base) Marshable lys)
                  -> (ys  : Local.Branches ks rs lys)
                  -> Type
    where
      R : (pzs : DList (String,Base) Marshable lzs)
       -> (zs  : Local.Branches ks rs lzs)
       -> (pf  : Meets       ks rs p px x pys ys pzs zs)
              -> MeetsResult ks rs p px x pys ys

  export
  meets : (f : (x : Local ks rs)
            -> (y : Local ks rs)
                 -> DecInfo () (DPair (Local ks rs) (p x y)))
      -> (px  : Marshable lx)
      -> (x   : Branch Local ks rs lx)
      -> (pys : DList (String,Base) Marshable lys)
      -> (ys  : Local.Branches ks rs lys)
             -> DecInfo ()
                        (MeetsResult ks rs p px x pys ys)

  meets f px x [] []
    = Yes (R [] [] Empty)

  meets f px x (ph :: pt) (h :: t)
    = case meet f px x ph h of
        (YesMeet (F la px') (B la ta cc) ** (Y pL pT y))
          => case meets f px x pt t of
               (Yes (R pzs zs pf))
                 => Yes (R (F la px' :: pzs) (B la ta cc :: zs) (MeetXY (Y pL pT y) pf))

               (No msg no)
                 => No ()
                       (\(R pzs zs pf)
                           => case pf of
                                (MeetXY z w) => no $ R _ _ w
                                (MeetNo z w) => no $ R _ _ w)

        (NoMeet ** (N pL))
          => case meets f px x pt t of
               (Yes (R pzs zs pf))
                 => Yes (R pzs zs (MeetNo (N pL) pf))
               (No msg no)
                 => No ()
                       (\(R pzs zs pf)
                           => case pf of
                                   (MeetXY y z) => no $ R _ _ z
                                   (MeetNo y z) => no $ R _ _ z)

        (Fail ** (FT pL pT))
          => No ()
                (\(R pzs zs pf)
                    => case pf of
                         (MeetXY y z)
                           => case y of
                                   (Y prf pT1 pM) => pT pT1
                         (MeetNo y z)
                           => case y of
                                   (N g) => g pL)

        (Fail ** (FM pL pT pM))
          => No ()
                (\(R pzs zs pf) =>
                    case pf of
                      (MeetXY y z) => case y of
                                        (Y prf pT1 w) => pM w
                      (MeetNo y z) => case y of
                                           (N g) => g pL)

||| A meeting between two list of branches is a collection of
||| successful ‘meets’. We use this proposition to record branch
||| intersection.
|||
namespace Meeting

  public export
  data Meeting : (ks : List Kind)
              -> (rs : List Role)
              -> (0 p : (x : Local ks rs)
                     -> (y : Local ks rs)
                     -> (z : Local ks rs)
                          -> Type)

              -> (px : DList (String,Base) Marshable lxs)
              -> (xs : Local.Branches ks rs lxs)
              -> (py : DList (String,Base) Marshable lys)
              -> (ys : Local.Branches ks rs lys)
              -> (pz : DList (String,Base) Marshable lzs)
              -> (zs : Local.Branches ks rs lzs)
              -> Type
    where
      Nil : Meeting ks rs p Nil Nil py ys Nil Nil

      (::) : {pas,pzs,zs, as : _}
          -> (pM  : Meets   ks rs p  px        x      pys ys         pzs              zs)
          -> (ltr : Meeting ks rs p      pxs      xs  pys ys             pas             as)
                 -> Meeting ks rs p (px::pxs) (x::xs) pys ys (append pzs pas) (append zs as)

  public export
  data Result : (ks : List Kind)
             -> (rs : List Role)
             -> (0 p : (x : Local ks rs)
                    -> (y : Local ks rs)
                    -> (z : Local ks rs)
                         -> Type)

             -> (px : DList (String,Base) Marshable lxs)
             -> (xs : Local.Branches ks rs lxs)
             -> (py : DList (String,Base) Marshable lys)
             -> (ys : Local.Branches ks rs lys)
                   -> Type
    where
      R : (pz  : DList (String,Base) Marshable lzs)
       -> (zs  : Local.Branches ks rs lzs)
       -> (prf : Meeting ks rs p px xs py ys pz zs)
              -> Result  ks rs p px xs py ys

  export
  meeting : (f : (x : Local ks rs)
              -> (y : Local ks rs)
                   -> DecInfo () (DPair (Local ks rs) (p x y)))
         -> (px : DList (String,Base) Marshable lxs)
         -> (xs : Local.Branches ks rs lxs)
         -> (py : DList (String,Base) Marshable lys)
         -> (ys : Local.Branches ks rs lys)
               -> DecInfo ()
                          (Result ks rs p px xs py ys)
  meeting f [] [] py ys
    = Yes (R _ _ Nil)

  meeting f (ph :: pt) (h :: t) py ys with (meets f ph h py ys)
    meeting f (ph :: pt) (h :: t) py ys | (Yes (R pzs zs pf)) with (meeting f pt t py ys)
      meeting f (ph :: pt) (h :: t) py ys | (Yes (R pzs zs pf)) | (Yes (R pz x prf))
        = Yes (R (append pzs pz) (append zs x) (pf :: prf))

      meeting f (ph :: pt) (h :: t) py ys | (Yes (R pzs zs pf)) | (No msg no)
        = No ()
             (\(R pzs zs prf)
               => case prf of
                    (pM :: ltr) => no $ R _ _ ltr)

    meeting f (ph :: pt) (h :: t) py ys | (No msg no)
      = No ()
           (\(R pzs zs prf)
             => case prf of
                  (pM :: ltr) => no $ R _ _ pM)


namespace Concat

  public export
  data Concat : (pw : DList (String,Base) Marshable iws)
             -> (ws : Local.Branches ks rs iws)
             -> (px : DList (String,Base) Marshable ixs)
             -> (xs : Local.Branches ks rs ixs)
             -> (py : DList (String,Base) Marshable iys)
             -> (ys : Local.Branches ks rs iys)
             -> (pz : DList (String,Base) Marshable izs)
             -> (zs : Local.Branches ks rs izs)
                   -> Type
    where
      YS : Concat Nil Nil Nil Nil py ys py ys

      AX : Concat Nil Nil      pxs       xs py ys      pz      zs
        -> Concat Nil Nil (px::pxs) (x::xs) py ys (px::pz) (x::zs)

      AW : Concat      pws      ws  px xs py ys      pz      zs
        -> Concat (pw::pws) (w::ws) px xs py ys (pw::pz) (w::zs)


  public export
  data Result : (pw : DList (String,Base) Marshable iws)
             -> (ws : Local.Branches ks rs iws)
             -> (px : DList (String,Base) Marshable ixs)
             -> (xs : Local.Branches ks rs ixs)
             -> (py : DList (String,Base) Marshable iys)
             -> (ys : Local.Branches ks rs iys)
                   -> Type
    where
      R : (pz : DList (String,Base) Marshable izs)
       -> (zs : Local.Branches ks rs izs)
       -> (pf : Concat pw ws px xs py ys pz zs)
             -> Result pw ws px xs py ys


  export
  concat : (pw : DList (String,Base) Marshable iws)
        -> (ws : Local.Branches ks rs iws)
        -> (px : DList (String,Base) Marshable ixs)
        -> (xs : Local.Branches ks rs ixs)
        -> (py : DList (String,Base) Marshable iys)
        -> (ys : Local.Branches ks rs iys)
              -> Result pw ws px xs py ys


  concat [] [] [] [] py ys
    = R py ys YS

  concat [] [] (px :: pxs) (x :: xs) py ys
    = let R pzs zs prf = concat Nil Nil pxs xs py ys
      in R (px::pzs) (x::zs) (AX prf)

  concat (pw :: pws) (w :: ws) px xs py ys
    = let R pzs zs prf = concat pws ws px xs py ys
      in R (pw::pzs) (w :: zs) (AW prf)

  public export
  data Least1 : (c : Concat pw ws px xs py ys pz zs)
             -> Type
    where
      One : {c : Concat pw ws px xs py ys (pz::pzs) (z::zs)} -> Least1 c

  empty : {c : Concat Nil Nil Nil Nil Nil Nil Nil Nil} -> Least1 c -> Void
  empty (One) impossible

  export
  least1 : {pz : _} -> {zs : _} -> (c : Concat pw ws px xs py ys pz zs)
        -> Dec (Least1 c)
  least1 {pz = []} {zs = []} YS = No empty
  least1 {pz = (py :: pz)} {zs = (y::ys)} YS = Yes One
  least1 {pz = (px :: pz)} {zs = (x :: zs)} (AX ax) = Yes One
  least1 {pz = (pw :: pz)} {zs = (w :: zs)} (AW ax) = Yes One


namespace Diff

  public export
  data Diff : (px : DList (String,Base) Marshable ltx)
           -> (xs : Local.Branches ks rs ltx)
           -> (py : DList (String,Base) Marshable lty)
           -> (ys : Local.Branches ks rs lty)
           -> (pz : DList (String,Base) Marshable ltz)
           -> (zs : Local.Branches ks rs ltz)
                 -> Type
    where
      Empty : Diff Nil Nil py ys Nil Nil

      Inc : (prf : SharedLabel ks rs x ys -> Void)
         -> (ltr : Diff      pxs      xs  pys ys      pzs      zs)
                -> Diff (px::pxs) (x::xs) pys ys (px::pzs) (x::zs)

      Skip : (prf : SharedLabel ks rs x ys)
          -> (ltr : Diff      pxs      xs  pys ys pzs zs)
                 -> Diff (px::pxs) (x::xs) pys ys pzs zs



  public export
  data Result : (px : DList (String,Base) Marshable ltx)
             -> (xs : Local.Branches ks rs ltx)
             -> (py : DList (String,Base) Marshable lty)
             -> (ys : Local.Branches ks rs lty)
                   -> Type
    where
      R : (pz : DList (String,Base) Marshable lzs)
       -> (zs : Local.Branches ks rs lzs)
       -> (pf : Diff   px xs py ys pz zs)
             -> Result px xs py ys

  export
  diff : (px : DList (String,Base) Marshable ltx)
      -> (xs : Local.Branches ks rs ltx)
      -> (py : DList (String,Base) Marshable lty)
      -> (ys : Local.Branches ks rs lty)
            -> Result px xs py ys
  diff [] [] py ys
    = R [] [] Empty

  diff (px :: pxs) (x :: xs) py ys with (sharedLabel x ys)
    diff (px :: pxs) (x :: xs) py ys | (Yes prf) with (diff pxs xs py ys)
      diff (px :: pxs) (x :: xs) py ys | (Yes prf) | (R pzs zs pf)
        = R pzs zs (Skip prf pf)

    diff (px :: pxs) (x :: xs) py ys | (No contra) with (diff pxs xs py ys)
      diff (px :: pxs) (x :: xs) py ys | (No contra) | (R pz zs pf)
        = R (px :: pz) (x :: zs) (Inc contra pf)

||| Merging Offers
|||
||| Offers in Capable are analgous to case-spliting (pattern matching) but with fixed top-level patterns that _must_ be covering.
||| Thus their merging must too be covering and exact in all instances that an offer is seen.
|||
namespace Offer

  public export
  data Merge : (ks : List Kind)
            -> (rs : List Role)
            -> (0 p : (x : Local ks rs)
                   -> (y : Local ks rs)
                   -> (z : Local ks rs)
                        -> Type)

            -> (px     : DList (String,Base) Marshable lxs)
            -> (these  : Local.Branches ks rs lxs)
            -> (py     : DList (String,Base) Marshable lys)
            -> (those  : Local.Branches ks rs lys)
            -> (result : Local.Branches ks rs lxs)
                      -> Type
    where

      Nil : Merge ks rs p Nil Nil Nil Nil Nil

      (::) : (pH : Meet  ks rs p  px        this          py        that        (YesMeet px result))
          -> (pT : Merge ks rs p      pxs         these       pys         those                  results)
                -> Merge ks rs p (px::pxs) (this::these) (py::pys) (that::those)        (result::results)

  public export
  data Result : (ks : List Kind)
             -> (rs : List Role)
             -> (0 p : (x : Local ks rs)
                    -> (y : Local ks rs)
                    -> (z : Local ks rs)
                         -> Type)
             -> (pm : DList (String,Base) Marshable lxs)
             -> (xs : Local.Branches ks rs lxs)
             -> (py : DList (String,Base) Marshable lys)
             -> (ys : Local.Branches ks rs lys)
                   -> Type
    where
      R : (zs  : Local.Branches ks rs lxs)
       -> (prf : Merge  ks rs p px xs py ys zs)
              -> Result ks rs p px xs py ys

  isLeftHeavy : Merge ks rs p (px::pxs) (x::xs) Nil Nil zs -> Void
  isLeftHeavy _ impossible


  isRightHeavy : Merge ks rs p Nil Nil (py::pys) (y::ys) zs -> Void
  isRightHeavy _ impossible

  export
  merge : (f : (x : Local ks rs)
            -> (y : Local ks rs)
                 -> DecInfo () (DPair (Local ks rs) (p x y)))

       -> (px : DList (String,Base) Marshable lxs)
       -> (xs : Local.Branches ks rs lxs)
       -> (py : DList (String,Base) Marshable lys)
       -> (ys : Local.Branches ks rs lys)

             -> DecInfo ()
                        (Offer.Result ks rs p px xs py ys)


  merge f px xs py ys with (shape xs ys)
    merge f [] [] [] [] | Empty
      = Yes (R [] [])

    merge f (px::pxs) (x :: xs) [] [] | LH
      = No () (\case (R zs prf) => isLeftHeavy prf)

    merge f [] [] (px::pxs) (x :: xs) | RH
      = No () (\case (R zs prf) => isRightHeavy prf)

    merge f (px::pxs) (x :: xs) (py :: pys) (y :: ys) | Same
      = case meet f px x py y of
             ((YesMeet (F la px) (B la ta cc)) ** Y Refl Refl z)
               => case merge f pxs xs pys ys of
                       (Yes (R zs prf)) => Yes (R (B la ta cc :: zs) (Y Refl Refl z :: prf))
                       (No msg no)
                         => No ()
                               (\(R zs prf) => case prf of
                                                 (_ :: ltr) => no $ R _ ltr)
             (NoMeet ** snd)
               => case snd of
                       (N pL)
                         => No () (\(R zs prf) => case prf of
                                                       ((Y Refl Refl pM) :: pT) => pL Refl)
             (Fail ** snd)
               => case snd of
                    (FT pL pT)
                      => No ()
                            (\(R zs prf)
                               => case prf of
                                       ((Y Refl Refl pM) :: z) => pT Refl)
                    (FM Refl Refl pM)
                      => No ()
                            (\(R zs prf)
                              => case prf of
                                      ((Y Refl Refl z) :: pT) => pM z)

namespace Protocol
  public export
  data Merge : (this, that, result : Local ks rs)
                                  -> Type
    where
      End  : Merge End End End
      Call : Merge (Call a) (Call a) (Call a)
      Crash : Merge Crash Crash Crash
      Rec : Merge this that result
         -> Merge (Rec a this)
                  (Rec a that)
                  (Rec a result)

      Offer : Offer.Merge ks rs Protocol.Merge pm these pm those result
           -> Merge (ChoiceL BRANCH w ty (UNION pm) these)
                    (ChoiceL BRANCH w ty (UNION pm) those)
                    (ChoiceL BRANCH w ty (UNION pm) result)

      Select : {shared, pmC, r,ps, result: _}
            -> Diff pmA these pmB those pmL lefts
            -> Diff pmB those pmA these pmR rights
            -> Meeting ks rs Merge pmA these pmB those pmC shared
            -> (pc : Concat pmC shared pmL lefts pmR rights (p::ps) (r::result))
            -> Least1 pc
            -> Merge (ChoiceL SELECT w tyA (UNION pmA) these)
                     (ChoiceL SELECT w tyB (UNION pmB) those)
                     (ChoiceL SELECT w tyC (UNION (p::ps))  (r::result))


  diffHeads : {this,that : _} -> (SameShapedHead this that -> Void) -> (Merge this that res) -> Void
  diffHeads f End = f (SS End)
  diffHeads f Call = f (SS Call)
  diffHeads f (Rec x) = f (SS Rec)
  diffHeads f (Crash) = f (SS Crash)
  diffHeads f (Offer x) = f (SS Offer)
  diffHeads f (Select x y z pc _) = f (SS Select)

  export
  merge : (this, that : Local ks rs)
                     -> DecInfo ()
                                (DPair (Local ks rs)
                                       (Merge this that))
  merge this that with (sameShapedHead this that)
    merge this that | (Yes (SS ss)) with (ss)
      merge Crash Crash | (Yes (SS ss)) | Crash
        = Yes (Crash ** Crash)

      merge End End | (Yes (SS ss)) | End
        = Yes (End ** End)

      merge (Call prfA) (Call prfB) | (Yes (SS ss)) | Call
        = case Index.decEq prfA prfB of
            (Yes (Same Refl Refl))
              => Yes (Call prfB ** Call)
            (No no)
              => No ()
                    (\(_ ** Call) => no (Same Refl Refl))

      merge (Rec a kA) (Rec b kB) | (Yes (SS ss)) | Rec
        = case decEq a b of
            (Yes Refl)
              => case merge kA kB of
                   (Yes (z ** prf))
                     => Yes (Rec b z ** Rec prf)
                   (No msg no)
                     => No ()
                           (\(Rec _ ltr ** Rec prf) => no (ltr ** prf))
            (No no)
              => No ()
                    (\(_ ** Rec ltr) => no Refl)

      merge (ChoiceL BRANCH wB (Val (UNION (f:::fs))) (UNION prfB) cbs)
            (ChoiceL BRANCH wA (Val (UNION (g:::gs))) (UNION prfA) cas) | (Yes (SS ss)) | Offer
        = case Index.decEq wB wA of
            (Yes (Same Refl Refl))
              => case decEq (UNION (f:::fs)) (UNION (g:::gs)) of
                  (Yes Refl)
                    => case decEq prfB prfA Refl of
                        Refl =>
                          case assert_total $ Offer.merge Protocol.merge prfB cbs prfA cas of
                               (Yes (R zs prf)) => Yes (ChoiceL BRANCH _ _ _ zs ** Offer prf)
                               (No msg no)
                                 => No ()
                                       (\(_ ** Offer prf) => no $ R _ prf)
                  (No no)
                    => No ()
                          (\(_ ** Offer _) => no Refl)
            (No no)
              => No ()
                    (\(_ ** Offer _) => no (Same Refl Refl))

      merge (ChoiceL SELECT wB typeB (UNION prfB) cbs)
            (ChoiceL SELECT wA typeA (UNION prfA) cas) | (Yes (SS ss)) | Select
        = case Index.decEq wB wA of
            (Yes (Same Refl Refl))
              => let R pl ls prfL = diff prfB cbs prfA cas in
                 let R pr rs prfR = diff prfA cas prfB cbs in
                   case assert_total $ meeting Protocol.merge prfB cbs prfA cas of
                     (Yes (R ps ss prfS))
                       => case concat ps ss pl ls pr rs of
                            R pzs zs prfC =>
                              case least1 prfC of
                                (Yes (One))
                                  => Yes (ChoiceL SELECT wA _ (UNION pzs) zs ** Select prfL prfR prfS prfC One)
                                (No contra)
                                  => No ()
                                        (\(_ ** Select _ _ _ _ One) => believe_me ?askTheGaul)
--                            R [] [] prfC => No () (\(_ ** Select _ _ _ _) => )
--                            R (pz::pzs) (z :: zs) prfC
--                              => Yes (ChoiceL SELECT _ (Val $ UNION _) (UNION _) _ ** Select prfL prfR prfS prfC)
--                            case isSucc zs of
--                              (Yes x) => ?as_0
--                              (No no)
--                                => No ()
--                                      (\(_ ** Select _ _ _ c) => no ?a)
                     (No msg no)
                       => No ()
                             (\(_ ** Select _ _ m _ _) => no $ R _ _ m)

            (No no)
              => No ()
                    (\(_ ** Select _ _ _ _ _) => no (Same Refl Refl))


    merge this that | (No contra)
      = No ()
           (\(z ** prf) => diffHeads contra prf)

namespace Many


  public export
  data Merge : (these : Local.Branches ks rs lxs)
            -> (res   : Local ks rs)
                     -> Type
    where
      Singleton : Many.Merge [B la ta c] c

      Split : {result, this : _} -> Many.Merge xs this
           -> Merge x y result
           -> Merge result this fi
           -> Many.Merge (B la ta x::(B lb tb y::xs)) fi

  Uninhabited (Many.Merge Nil res) where
    uninhabited _ impossible

  export
  merge : (these : Local.Branches ks rs lxs)
                -> DecInfo ()
                           (DPair (Local ks rs)
                                  (Merge these))
  merge []
    = No () (\(_ ** prf) => absurd prf)

  merge (B _ _ c::[])
    = Yes (c ** Singleton)

  merge (B _ _ x::(B _ _ y :: ys)) with (merge x y)
    merge (B _ _ x::(B _ _ y :: ys)) | (Yes (intr ** pH)) with (merge ys)
      merge (B _ _ x::(B _ _ y :: ys)) | (Yes (intr ** pH)) | (Yes (ltr ** pltr))
        = case merge intr ltr of
            (Yes (l ** pR))
              => Yes (l ** Split pltr pH pR)
            (No msg no)
              => No ()
                    (\case (fst ** (Split z w v)) => no ?manyMerge)

      merge (B _ _ x::(B _ _ y :: ys)) | (Yes (intr ** pH)) | (No msg no)
        = No ()
             (\(_ ** Split pltr _ _) => no (_ ** pltr))
    merge (B _ _ x::(B _ _ y :: ys)) | (No msg no)
      = No ()
           (\(_ ** Split _ ph pt) => no (_ ** ph))
-- [ EOF ]
