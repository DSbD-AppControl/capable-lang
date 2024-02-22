|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Capable.Types.Protocol.Projection

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

import Capable.Types.Protocol.Global
import Capable.Types.Protocol.Local

%default total

mutual
  namespace Protocol
    ||| Plain projection
    public export
    data Project : (ks   : List Kind)
                -> (rs   : List Role)
                -> (whom : Role rs w)
                -> (g    : Global ks rs)
                -> (l    : Local  ks rs)
                        -> Type
      where
        End  : Project ks rs whom End End

        Call : Project ks rs whom (Call idx) (Call idx)

        Rec : (rec : Project (k::ks) rs whom      x       y)
                  -> Project ks rs whom (Rec k x) (Rec k y)

        Select : (prf : Equals Role (IsVar rs) whom s)
              -> (bs  : Branches.Project ks rs whom                               (x::xs) (y::ys))
                     -> Protocol.Project ks rs whom (ChoiceG        s r t p notsr (x::xs))
                                                    (ChoiceL SELECT   r t p               (y::ys))

        Offer : (prf : Equals Role (IsVar rs) whom r)
             -> (bs  : Branches.Project ks rs whom                               (x::xs) (y::ys))
                    -> Protocol.Project ks rs whom (ChoiceG         s r t p notstr (x::xs))
                                                   (ChoiceL  BRANCH s   t p                (y::ys))

        Merge : (prfS  : Not (Equals Role (IsVar rs) whom s))
             -> (prfR  : Not (Equals Role (IsVar rs) whom r))
             -> (prf   : Same ks rs whom (g::gs) (B l t' c))
                      -> Project ks rs whom (ChoiceG s r t p notsr (g::gs))
                                             c

  namespace Branch

      public export
      data Project : (ks : List Kind)
                  -> (rs : List Role)
                  -> (role   : Role rs r)
                  -> (global : Branch Global ks rs l)
                  -> (local  : Branch Local  ks rs l)
                            -> Type
        where
          B : (m : String)
           -> (t : Base)
                -> Protocol.Project ks rs whom        g         l
                ->   Branch.Project ks rs whom (B m t g) (B m t l)

  namespace Branches

    public export
    data Project : (ks : List Kind)
                -> (rs : List Role)
                -> (role : Role rs w)
                -> (gs   : Global.Branches ks rs lts)
                -> (ls   :  Local.Branches ks rs lts)
                        -> Type
      where
        Nil : Project ks rs whom Nil Nil

        (::) : Branch.Project ks rs whom x y
            -> Branches.Project ks rs whom xs ys
            -> Branches.Project ks rs whom (x::xs) (y::ys)


    public export
    data Same : (ks : List Kind)
             -> (rs : List Role)
             -> (role : Role rs w)
             -> (gs   : Global.Branches ks rs ltss)
             -> (l    : Branch Local    ks rs lts)
                      -> Type
      where
        S : {l : _}
         -> {ls : _}
         -> (projs : Branches.Project ks rs whom (g::gs) (l::ls))
         -> (prf   : All (String,Base)
                         (Branch Local ks rs)
                         (BranchEQ l)
                         ll
                         ls)
                  -> Same ks rs whom (g::gs) l

mutual

  namespace Protocol
    export
    funProject : Protocol.Project ks rs whom b x
              -> Protocol.Project ks rs whom b y
              -> x === y

    funProject End End
      = Refl

    funProject Call Call
      = Refl

    funProject (Rec rec) (Rec z)
      = cong (Rec _) (funProject rec z)

    funProject (Select {ys = ys1} (Same Refl Refl) ps)
               (Select {ys = ys2} (Same Refl Refl) qs)
      = cong (ChoiceL SELECT _ _ _)
             (funProject ps qs)

    funProject (Select {notsr} (Same Refl Refl) bs)
               (Offer          (Same Refl Refl) w)
      = void (notSame notsr (Same Refl Refl))

    funProject (Select (Same Refl Refl) bs)
               (Merge prfS prfR z)
      = void (prfS (Same Refl Refl))

    funProject (Offer          (Same Refl Refl) bs)
               (Select {notsr} (Same Refl Refl) w)
      = void (notSame notsr (Same Refl Refl))

    funProject (Offer _ p) (Offer _ q)
      = cong (ChoiceL BRANCH _ _ _)
             (funProject p q)

    funProject (Offer (Same Refl Refl) bs)
               (Merge prfS prfR z)
      = void (prfR (Same Refl Refl))

    funProject (Merge prfS prfR prf)
               (Select (Same Refl Refl) bs)
      = void (prfS (Same Refl Refl))

    funProject (Merge prfS prfR prf)
               (Offer (Same Refl Refl) bs)
      = void (prfR (Same Refl Refl))

    funProject (Merge _ _ p) (Merge _ _ q)
      = funSame p q


  namespace Branch
    export
    funProject : Branch.Project ks rs whom b x
              -> Branch.Project ks rs whom b y
              -> x === y
    funProject (B m t p) (B m t q)
      = cong (B m t)
             (funProject p q)

  namespace Branches

    export
    funProject : Branches.Project ks rs whom b x
              -> Branches.Project ks rs whom b y
              -> x === y
    funProject [] []
      = Refl
    funProject (p :: ps) (q :: qs)
      = cong2 (::)
              (funProject p  q)
              (funProject ps qs)

    export
    funSame : Same ks rs whom gs (B l1 t1 x)
           -> Same ks rs whom gs (B l2 t2 y)
           -> x === y
    funSame (S (p :: ps) eqp) (S (q :: qs) eqq)
      = case funProject p q of Refl => Refl


mutual
  namespace Protocol
    export
    project : {ks, rs, w : _}
           -> (whom : Role rs w)
           -> (type : Global ks rs)
                   -> DecInfo Projection.Error
                              (DPair (Local   ks rs)
                                     (Project ks rs whom type))
    project whom End
      = Yes (End ** End)

    project whom (Call x)
      = Yes (Call x ** Call)

    project whom (Rec v x) with (project whom x)
      project whom (Rec v x) | (Yes (l ** prf))
        = Yes (Rec v l ** Rec prf)
      project whom (Rec v x) | (No msgWhyNot prfWhyNot)
        = No (Rec msgWhyNot)
             (\case (Rec v y ** Rec rec) => prfWhyNot (y ** rec))

    project whom (ChoiceG s x type prfM prfR opties) with (involved whom s x)

      -- [ NOTE ] Sender
      project s (ChoiceG s x type prfM prfR (b :: bs)) | (Sends Refl) with (Branches.project s (b::bs))
        project s (ChoiceG s x type prfM prfR (b :: bs)) | (Sends Refl) | (Yes (((y :: ys) ** (z :: zs))))
          = Yes (_ ** Select (Same Refl Refl) (z::zs))

        project s (ChoiceG s x type prfM prfR (b :: bs)) | (Sends Refl) | (No msg no)
          = No (Select msg)
               (\case (_ ** Select prf x) => no (_ ** x)
                      (_ ** Offer  prf x) => no (_ ** x)
                      (_ ** Merge f prfR prf) => f (Same Refl Refl))

      -- [ NOTE ] Receiving
      project x (ChoiceG s x type prfM prfR (b :: bs)) | (Recvs Refl) with (Branches.project x (b::bs))
        project x (ChoiceG s x type prfM prfR (b :: bs)) | (Recvs Refl) | (Yes ((y::ys) ** (z::zs)))
          = Yes (_ ** Offer (Same Refl Refl) (z::zs))

        project x (ChoiceG s x type prfM prfR (b :: bs)) | (Recvs Refl) | (No msg no)
          = No (Offer msg)
               (\case (_ ** (Select prf x)) => no (_ ** x)
                      (_ ** (Offer prf x)) => no (_ ** x)
                      (_ ** (Merge prfS prfR prf)) => prfR (Same Refl Refl))

      -- [ NOTE ] Not involved
      project whom (ChoiceG s x type prfM prfR ((B l b cont) :: bs)) | (Skips prfSNot prfRNot) with (same whom (B l b cont :: bs))
        project whom (ChoiceG s x type prfM prfR ((B l b cont) :: bs)) | (Skips prfSNot prfRNot) | (Yes (((B l b z) ** (S projs prf))))
          = Yes (_ ** Merge prfSNot prfRNot (S projs prf))

        project whom (ChoiceG s x type prfM prfR ((B l b cont) :: bs)) | (Skips prfSNot prfRNot) | (No msg no)
          = No (Skip msg)
               (\case (_ ** (Select prf y)) => prfSNot prf
                      (_ ** (Offer prf y)) => prfRNot prf
                      (_ ** (Merge prfS f (S projs prf))) => no (_ ** (S projs prf)))


  namespace Branch
    export
    project : {ks, s, rs, w: _}
           -> (whom : Role rs w)
           -> (g  : Branch Global ks rs (s,t))
                   -> DecInfo Projection.Error
                              (DPair (Branch Local ks rs (s,t))
                                     (Project ks rs whom g))
    project whom (B s t cont) with (project whom cont)
      project whom (B s t cont) | (Yes (l ** prf))
        = Yes (B s t l ** B s t prf)
      project whom (B s t cont) | (No msg no)
        = No (BranchNotProjectionable s msg)
             (\case ((B s t l) ** (B s t y)) => no (l ** y))

  namespace Branches
    export
    project : {ks, lts, rs, w: _}
           -> (whom : Role rs w)
           -> (bs   : Global.Branches ks rs lts)
                     -> DecInfo Projection.Error
                                (DPair (Local.Branches ks rs lts)
                                       (Project ks rs whom bs))
    project whom []
      = Yes ([] ** [])

    project whom ((B l b cont) :: rest) with (project whom (B l b cont))
      project whom ((B l b cont) :: rest) | (Yes (lp ** prf)) with (project whom rest)
        project whom ((B l b cont) :: rest) | (Yes (lp ** prf)) | (Yes (lps ** prfs))
          = Yes (lp :: lps ** prf :: prfs)
        project whom ((B l b cont) :: rest) | (Yes (lp ** prf)) | (No msg no)
          = No msg
               (\case ((y :: ys) ** (z :: zs)) => no (ys ** zs))

      project whom ((B l b cont) :: rest) | (No msg no)
        = No msg
             (\case ((y :: ys) ** (z :: zs)) => no (y ** z))

  namespace Same

    export
    same : {w, ks, l,s : _}
        -> {ls,rs : _}
        -> (whom : Role rs w)
        -> (bs   : Global.Branches ks rs ((l,s) :: ls))
                -> DecInfo Projection.Error
                           (DPair (Branch Local ks rs (l,s))
                                  (Same ks rs whom bs))
    same whom bs with (project whom bs)
      same whom (x :: xs) | (Yes ((y :: ys) ** (z :: zs))) with (branchesEQ y ys)
        same whom (x :: xs) | (Yes ((y :: ys) ** (z :: zs))) | (Yes prfWhy)
          = Yes (y ** S (z :: zs) prfWhy)
        same whom (x :: xs) | (Yes ((y :: ys) ** (z :: zs))) | (No msg no)
          = No (NotAllSame (y::ys))
               (\case (fst ** (S (w :: v) prf))
                      => no $ rewrite sym (funProject w z) in
                              rewrite sym (funProject v zs) in prf)
      same whom bs | (No msg no)
        = No msg
             (\case (fst ** (S projs prf)) => no (fst :: _ ** projs))




namespace Closed
  export
  project : {w : _}
         -> {rs : List Role}
         -> (whom : Role rs w)
         -> (type : Global Nil rs)
                 -> DecInfo Projection.Error
                            (DPair (Local Nil rs)
                                   (Project Nil rs whom type))
  project
    = Protocol.project

-- [ EOF ]
