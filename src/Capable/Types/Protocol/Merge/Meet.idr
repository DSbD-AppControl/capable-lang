module Capable.Types.Protocol.Merge.Meet

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
            -> Meet ks rs p (F la px) (B la ta ca)
                            (F lb py) (B lb tb cb)
                            Fail


export
meet : (f : (x : Local ks rs)
         -> (y : Local ks rs)
              -> Either Merge.Error  (DPair (Local ks rs) (p x y)))

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
                    (Right (cz ** prf))
                      => (YesMeet (F ly px) (B ly ty cz) ** Y Refl Refl prf)

                    (Left msg )
                      => (Fail ** FM Refl Refl)

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
      R : {lzs : _}
       -> (pzs : DList (String,Base) Marshable lzs)
       -> (zs  : Local.Branches ks rs lzs)
       -> (pf  : Meets       ks rs p px x pys ys pzs zs)
              -> MeetsResult ks rs p px x pys ys

  export
  meets : (f : (x : Local ks rs)
            -> (y : Local ks rs)
                 -> Either Merge.Error (DPair (Local ks rs) (p x y)))
      -> (px  : Marshable lx)
      -> (x   : Branch Local ks rs lx)
      -> (pys : DList (String,Base) Marshable lys)
      -> (ys  : Local.Branches ks rs lys)
             -> Either Merge.Error
                       (MeetsResult ks rs p px x pys ys)

  meets f px x [] []
    = Right (R [] [] Empty)

  meets f px x (ph :: pt) (h :: t)
    = case meet f px x ph h of
        (YesMeet (F la px') (B la ta cc) ** (Y pL pT y))
          => case meets f px x pt t of
               (Right (R pzs zs pf))
                 => Right (R (F la px' :: pzs)
                             (B la ta cc :: zs)
                             (MeetXY (Y pL pT y) pf))

               (Left msg )
                 => Left (MeetFailCont la msg)

        (NoMeet ** (N pL))
          => case meets f px x pt t of
               (Right (R pzs zs pf))
                 => Right (R pzs zs (MeetNo (N pL) pf))
               (Left msg )
                 => Left msg

        (Fail ** (FT pL pT))
          => Left (MeetFail (MkPair x h))

        (Fail ** (FM pL pT))
          => Left (MeetFail (MkPair x h))

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
      R : {lzs : _}
       -> (pz  : DList (String,Base) Marshable lzs)
       -> (zs  : Local.Branches ks rs lzs)
       -> (prf : Meeting ks rs p px xs py ys pz zs)
              -> Result  ks rs p px xs py ys

  export
  meeting : (f : (x : Local ks rs)
              -> (y : Local ks rs)
                   -> Either Merge.Error (DPair (Local ks rs) (p x y)))
         -> (px : DList (String,Base) Marshable lxs)
         -> (xs : Local.Branches ks rs lxs)
         -> (py : DList (String,Base) Marshable lys)
         -> (ys : Local.Branches ks rs lys)
               -> Either Merge.Error
                          (Result ks rs p px xs py ys)
  meeting f [] [] py ys
    = Right (R _ _ Nil)

  meeting f (ph :: pt) (h :: t) py ys with (meets f ph h py ys)
    meeting f (ph :: pt) (h :: t) py ys | (Right (R pzs zs pf)) with (meeting f pt t py ys)
      meeting f (ph :: pt) (h :: t) py ys | (Right (R pzs zs pf)) | (Right (R pz x prf))
        = Right (R (append pzs pz) (append zs x) (pf :: prf))

      meeting f (ph :: pt) (h :: t) py ys | (Right (R pzs zs pf)) | (Left msg )
        = Left msg

    meeting f (ph :: pt) (h :: t) py ys | (Left msg )
      = Left (msg)

-- [ EOF ]
