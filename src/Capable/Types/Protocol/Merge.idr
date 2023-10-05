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
import Capable.Types.Protocol.Merge.Meet
import Capable.Types.Protocol.Merge.Concat
import Capable.Types.Protocol.Merge.Diff

import Debug.Trace

%default total

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
                 -> Either Merge.Error
                           (DPair (Local ks rs) (p x y)))

       -> (px : DList (String,Base) Marshable lxs)
       -> (xs : Local.Branches ks rs lxs)
       -> (py : DList (String,Base) Marshable lys)
       -> (ys : Local.Branches ks rs lys)

             -> Either Merge.Error
                       (Offer.Result ks rs p px xs py ys)


  merge f px xs py ys with (shape xs ys)
    merge f [] [] [] [] | Empty
      = Right (R [] [])

    merge f (px::pxs) (x :: xs) [] [] | LH
      = Left (UnBalancedOffers True)

    merge f [] [] (px::pxs) (x :: xs) | RH
      = Left (UnBalancedOffers False)

    merge f (px::pxs) (x :: xs) (py :: pys) (y :: ys) | Same
      = case meet f px x py y of
             ((YesMeet (F la px) (B la ta cc)) ** Y Refl Refl z)
               => case merge f pxs xs pys ys of
                       (Right (R zs prf))
                         => Right (R (B la ta cc :: zs)
                                     (Y Refl Refl z :: prf))
                       (Left msg)
                         => Left (MeetFailCont la msg)

             (NoMeet ** snd)
               => case snd of
                       (N pL)
                         => Left (MeetFail (MkPair x y))
             (Fail ** snd)
               => case snd of
                    (FT pL pT)
                      => Left (MeetFail (MkPair x y))
                    (FM Refl Refl)
                      => Left (MeetFail (MkPair x y))


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

      Select : Diff pmA these pmB those pmL lefts
            -> Diff pmB those pmA these pmR rights
            -> Meeting ks rs Merge pmA these pmB those pmC shared
            -> Append xs pmL lefts
                      ys pmR rights
                      zs pmZ leftrights
            -> Append zs pmZ leftrights
                      ws pmC shared
                      (lr::lrs) (pr::prs) (br::brs)
            -> Merge (ChoiceL SELECT w tyA (UNION pmA) these)
                     (ChoiceL SELECT w tyB (UNION pmB) those)
                     (ChoiceL SELECT w (Val (UNION (lr:::lrs))) (UNION (pr::prs))  (br::brs))


  diffHeads : {this,that : _}
           -> (SameShapedHead this that -> Void)
           -> (Merge this that res)
           -> Void
  diffHeads f End = f (SS End)
  diffHeads f Call = f (SS Call)
  diffHeads f (Rec x) = f (SS Rec)
  diffHeads f (Crash) = f (SS Crash)
  diffHeads f (Offer x) = f (SS Offer)
  diffHeads f (Select x y z q pc) = f (SS Select)

  export
  merge : (this, that : Local ks rs)
                     -> Either Merge.Error
                                (DPair (Local ks rs)
                                       (Merge this that))
  merge this that with (sameShapedHead this that)
    merge this that | (Yes (SS ss)) with (ss)
      merge Crash Crash | (Yes (SS ss)) | Crash
        = Right (Crash ** Crash)

      merge End End | (Yes (SS ss)) | End
        = Right (End ** End)

      merge (Call prfA) (Call prfB) | (Yes (SS ss)) | Call
        = case Index.decEq prfA prfB of
            (Yes (Same Refl Refl))
              => Right (Call prfB ** Call)
            (No no)
              => Left WrongRecVar

      merge (Rec a kA) (Rec b kB) | (Yes (SS ss)) | Rec
        = case decEq a b of
            (Yes Refl)
              => case merge kA kB of
                   (Right (z ** prf))
                     => Right (Rec b z ** Rec prf)
                   (Left msg )
                     => Left (InRec msg)
            (No no)
              => Left WrongRecVar

      merge (ChoiceL BRANCH wB (Val (UNION (f:::fs))) (UNION prfB) cbs)
            (ChoiceL BRANCH wA (Val (UNION (g:::gs))) (UNION prfA) cas) | (Yes (SS ss)) | Offer
        = case Index.decEq wB wA of
            (Yes (Same Refl Refl))
              => case decEq (UNION (f:::fs)) (UNION (g:::gs)) of
                  (Yes Refl)
                    => case decEq prfB prfA Refl of
                        Refl =>
                          case assert_total $ Offer.merge Protocol.merge prfB cbs prfA cas of
                               (Right (R zs prf)) => Right (ChoiceL BRANCH wA (Val (UNION (g ::: gs))) (UNION prfA) zs ** Offer prf)
                               (Left msg )
                                 => Left (OffersFail msg)

                  (No no)
                    => Left (TypeMismatch (UNION (f:::fs)) (UNION (g:::gs)))
            (No no)
              => Left (RoleMismatch)

      merge (ChoiceL SELECT wB typeB (UNION prfB) cbs)
            (ChoiceL SELECT wA typeA (UNION prfA) cas) | (Yes (SS ss)) | Select
        = case Index.decEq wB wA of
            (Yes (Same Refl Refl))
              => let R pl ls prfL = diff prfB cbs prfA cas in
                 let R pr rs prfR = diff prfA cas prfB cbs in
                   case assert_total $ meeting Protocol.merge prfB cbs prfA cas of
                     (Right (R ps ss prfS))
                       => case append pl ls pr rs of
                            R plrs blrs prfLR =>
                              case append plrs blrs ps ss of
                                R pzs  bzs  prfZ =>
                                  case prfZ of
                                    Empty => Left EmptySelect
                                    (Last _)
                                      => Right (ChoiceL SELECT wA (Val (UNION _)) (UNION (pzs)) (bzs) ** Select prfL prfR prfS prfLR prfZ)
                                    (Extend _)
                                      => Right (ChoiceL SELECT wA (Val (UNION _)) (UNION (pzs)) (bzs) ** Select prfL prfR prfS prfLR prfZ)

                     (Left msg )
                       => Left (Meeting msg)

            (No no)
              => Left (RoleMismatch)


    merge this that | (No contra)
      = Left NotMergable

namespace Many


  public export
  data Merge : (these : Local.Branches ks rs lxs)
            -> (res   : Local ks rs)
                     -> Type
    where
      Singleton : Many.Merge [B la ta c] c

      Twain : Merge x y fi
           -> Many.Merge (B la ta x::(B lb tb y::Nil)) fi

      Split : {result : Local ks rs}
           -> {this : _}
           -> Many.Merge xs this
           -> Merge x y result
           -> Merge result this fi
           -> Many.Merge (B la ta x::(B lb tb y::xs)) fi

  Uninhabited (Many.Merge Nil res) where
    uninhabited _ impossible

  export
  merge : (these : Local.Branches ks rs lxs)
                -> Either Merge.Error
                           (DPair (Local ks rs)
                                  (Merge these))
  merge []
    = Left EmptyFold

  merge (B _ _ x :: [])
    = Right (x ** Singleton)

  merge (B _ _ x :: (B _ _ y :: [])) with (merge x y)
    merge (B _ _ x :: (B _ _ y :: [])) | (Left err)
      = Left err

    merge (B _ _ x :: (B _ _ y :: [])) | (Right (z ** prf))
      = Right (z ** Twain prf)

  merge (B _ _ x :: (B _ _ y :: (z :: zs))) with (merge x y)
    merge (B _ _ x :: (B _ _ y :: (z :: zs))) | (Left err)
      = Left err

    merge (B _ _ x :: (B _ _ y :: (z :: zs))) | (Right (h ** pH)) with (assert_total $ merge (z::zs))
      merge (B _ _ x :: (B _ _ y :: (z :: zs))) | (Right (h ** pH)) | (Left err)
        = Left err
      merge (B _ _ x :: (B _ _ y :: (z :: zs))) | (Right (h ** pH)) | (Right (t ** pT)) with (merge h t)
        merge (B _ _ x :: (B _ _ y :: (z :: zs))) | (Right (h ** pH)) | (Right (t ** pT)) | (Left err)
          = Left err
        merge (B _ _ x :: (B _ _ y :: (z :: zs))) | (Right (h ** pH)) | (Right (t ** pT)) | (Right (q ** pQ))
          = Right (q ** Split pT pH pQ)


-- [ EOF ]
