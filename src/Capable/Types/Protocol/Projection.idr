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
import Capable.Types.Role
import Capable.Types.Base

import Capable.Types.Protocol

%default total

mutual
  namespace Protocol
    ||| Plain projection
    public export
    data Project : (ks   : List Kind)
                -> (rs   : List Role)
                -> (role : IsVar rs MkRole)
                -> (g    : Global ks rs)
                -> (l    : Local  ks rs)
                        -> Type
      where
        End  : Project ks rs whom End End

        Call : Project ks rs whom (Call idx) (Call idx)

        Rec : (rec : Project (R::ks) rs whom      x       y)
                  -> Project ks rs whom (Rec x) (Rec y)

        Select : (prf : Equals Role (IsVar rs) whom s)
              -> (bs  : Branches.Project ks rs whom                              (x::xs) (y::ys))
                     -> Protocol.Project ks rs whom (Choice        s r t p notsr (x::xs))
                                                    (Choice SELECT   r t p               (y::ys))

        Offer : (prf : Equals Role (IsVar rs) whom r)
             -> (bs  : Branches.Project ks rs whom                               (x::xs) (y::ys))
                    -> Protocol.Project ks rs whom (Choice        s r t p notstr (x::xs))
                                                   (Choice BRANCH s   t p                (y::ys))

        Merge : (prfS  : Not (Equals Role (IsVar rs) whom s))
             -> (prfR  : Not (Equals Role (IsVar rs) whom r))
             -> (prf   : Same ks rs whom (g::gs) (B l t' c))
                      -> Project ks rs whom (Choice s r t p notsr (g::gs))
                                             c

  namespace Branch

      public export
      data Project : (ks : List Kind)
                  -> (rs : List Role)
                  -> (role   : IsVar rs MkRole)
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
                -> (role : IsVar rs MkRole)
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
             -> (role : IsVar rs MkRole)
             -> (gs   : Global.Branches ks rs ltss)
             -> (l    : Branch Local    ks rs lts)
                      -> Type
      where
        S : {l : _}
         -> {ls : _}
         -> (projs : Branches.Project ks rs whom (g::gs) (l::ls))
         -> (prf   : All (String,Base) (Branch Local ks rs) (Equal l) ll ls)
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
      = cong Rec (funProject rec z)

    funProject (Select {ys = ys1} (Same Refl Refl) ps)
               (Select {ys = ys2} (Same Refl Refl) qs)
      = cong (Choice SELECT _ _ _)
             (funProject ps qs)

    funProject (Select {notsr} (Same Refl Refl) bs)
               (Offer          (Same Refl Refl) w)
      = void (notsr (Same Refl Refl))

    funProject (Select (Same Refl Refl) bs)
               (Merge prfS prfR z)
      = void (prfS (Same Refl Refl))

    funProject (Offer          (Same Refl Refl) bs)
               (Select {notsr} (Same Refl Refl) w)
      = void (notsr (Same Refl Refl))

    funProject (Offer _ p) (Offer _ q)
      = cong (Choice BRANCH _ _ _)
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

-- [ EOF ]
