||| Types as terms because we want to mirror real programmes.
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Capable.Terms.Protocols.Projection

import Decidable.Equality
import Toolkit.Decidable.Informative
import Toolkit.Decidable.Equality.Indexed

import Data.Singleton
import public Data.List.Elem
import public Data.List.Quantifiers

import public Data.List1
import public Data.List1.Quantifiers

import public Toolkit.Data.DList
import public Toolkit.Data.DList.All

import Capable.Error

import public Capable.Types
import public Capable.Types.Protocol
import public Capable.Types.Protocol.Projection
import public Capable.Types.Role
import        Capable.Terms.Vars
import        Capable.Terms.Roles
import        Capable.Terms.Types
import        Capable.Terms.Protocols

%default total
{-
namespace Protocl

  public export
  data Result : (ks : List Kind)
             -> (rs : List Role)
             -> (whom : DeBruijn.Role rs w)
             -> (global : Global ks rs)
                       -> Type
    where
      R :  (local : Local.Local ks rs)
        -> (proj  : Protocol.Project ks rs whom global local)
                 -> Result ks rs whom global


namespace Branch
  public export
  data Result : (ks : List Kind)
             -> (rs : List Role)
             -> (whom   : DeBruijn.Role rs w)
             -> (global : Branch Global ks rs (s,t))
                       -> Type
    where
      R : (l    : Branch Local.Local ks rs (s,t))
       -> (proj : Branch.Project ks rs whom g l)
               -> Result ks rs whom g

namespace Branches
  public export
  data Result : (ks : List Kind)
             -> (rs : List Role)
             -> (whom   : DeBruijn.Role rs w)
             -> (global : Global.Branches ks rs ls)
                       -> Type
    where
      R : (local : Local.Branches ks rs ls)
       -> (proj  : Branches.Project ks rs whom global local)
                -> Result ks rs whom global


  namespace Same
    public export
    data Result : (ks : List Kind)
               -> (rs : List Role)
               -> (whom   : DeBruijn.Role rs w)
               -> (global : Global.Branches ks rs ls)
                         -> Type
      where
        R : (l    : _)
         -> (proj : Same ks rs whom (g::gs) l)
                 -> Result ks rs whom (g::gs)

mutual

  export
  project : {rs,ks,w : _}
         -> {global : Global ks rs}
         -> (whom : DeBruijn.Role rs w)
         -> (type : Global ks ts rs ss global)
                 -> DecInfo Projection.Error
                            (Result ks rs whom global)
  project whom End
    = Yes (R _ End)

  project whom (Call prf)
    = Yes (R _ Call)

  project whom (Rec type) with (project whom type)
    project whom (Rec type) | (Yes (R l proj))
      = Yes (R (Rec _ l) (Rec proj))

    project whom (Rec type) | (No msg no)
      = No (Rec msg)
           (\(R (Rec _ a) (Rec this)) => no (R a this))

  project whom (Choice s r noSR t p bs) with (involved whom s r)

    -- [ NOTE ] Sender
    project whom (Choice s r noSR t p (b::bs)) | (Sends prfS) with (Branches.project s (b::bs))
      project s (Choice s r noSR t p (b::bs)) | (Sends Refl) | (Yes (R (elem :: rest) (x :: y)))
        = Yes (R _ (Select (Same Refl Refl) (x :: y)))
      project s (Choice s r noSR t p (b::bs)) | (Sends Refl) | (No msg no)
        = No (Select msg)
             (\case (R _ (Select prf x)) => no (R _ x)
                    (R _ (Offer prf x)) => no (R _ x)
                    (R _ (Merge f prfR prf))  => f (Same Refl Refl))

    -- [ NOTE ] Receiving
    project r (Choice s r noSR t p (b :: bs)) | (Recvs Refl) with (Branches.project r (b::bs))
      project r (Choice s r noSR t p (b :: bs)) | (Recvs Refl) | (Yes (R (elem :: rest) (x :: y)))
        = Yes (R _ (Offer (Same Refl Refl) (x::y)))


      project r (Choice s r noSR t p (b :: bs)) | (Recvs Refl) | (No msg no)
        = No (Offer msg)
             (\case (R _ (Select prf x)) => no (R _ x)
                    (R _ (Offer prf x)) => no (R _ x)
                    (R _ (Merge prfS prfR prf)) => prfR (Same Refl Refl))


    -- [ NOTE ] Not involved
    project whom (Choice s r noSR t p (b :: bs)) | (Skips prfSNot prfRNot) with (same whom (b::bs))
      project whom (Choice s r noSR t p (b :: bs)) | (Skips prfSNot prfRNot) | (Yes (R (B l t' c) (S projs prf)))
        = Yes (R _ (Merge prfSNot prfRNot (S projs prf)))

      project whom (Choice s r noSR t p (b :: bs)) | (Skips prfSNot prfRNot) | (No msg no)
        = No (Skip msg)
             (\case (R _ (Select prf x)) => prfSNot prf
                    (R _ (Offer prf x)) => prfRNot prf
                    (R _ (Merge prfS prfR (S projs prf))) => no (R _ (S projs prf)))

  namespace Branch
    export
    project : {s,w,rs : _}
           -> {ks : _}
           -> (whom : DeBruijn.Role rs w)
           -> {g  : Branch Global ks    rs (s,t)}
           -> (type : Global.Branch ks ts rs ss g)
                   -> DecInfo Projection.Error
                              (Branch.Result ks rs whom g)
    project whom (B s type choice) with (project whom choice)
      project whom (B s type choice) | (Yes (R local proj))
        = Yes (R (B s t local) (B s t proj))

      project whom (B s type choice) | (No msg no)
        = No (BranchNotProjectionable s msg)
             (\case (R (B s t l) (B s t y)) => no (R l y))

  namespace Branches
    export
    project : {lts : _}
           -> {rs : _}
           -> {ks : _}
           -> {w : _}
           -> (  whom : DeBruijn.Role rs w)
           -> {bs   : Global.Branches ks rs lts}
           -> (type   : Branches ks ts rs ss bs)
                     -> DecInfo Projection.Error
                                (Branches.Result ks rs whom bs)
    project whom []
      = Yes (R [] [])

    project whom (x :: xs) with (project whom x)
      project whom (x :: xs) | (Yes (R l p)) with (project whom xs)
        project whom (x :: xs) | (Yes (R l p)) | (Yes (R ls ps))
          = Yes (R (l :: ls) (p :: ps))
        project whom (x :: xs) | (Yes (R l p)) | (No msg no)
          = No msg
               (\case (R (y :: ys) (z :: zs)) => no (R ys zs))

      project whom (x :: xs) | (No msg no)
        = No msg (\case (R (y :: ys) (z :: zs)) => no (R y z))

  namespace Same

    export
    same : {l,s : _}
        -> {ls,rs : _}
        -> {ks : _}
        -> {w  : _}
        -> {b    : Branch Global   ks rs (l,s)}
        -> {bs   : Global.Branches ks rs ls}
        -> (  whom : DeBruijn.Role rs w)
        -> (  gs   : Branches ks ts rs ss (b::bs))
                  -> DecInfo Projection.Error
                             (Same.Result ks rs whom (b::bs))
    same whom gs with (Branches.project whom gs)
      same whom gs | (Yes (R (l' :: ls') (b' :: bs'))) with (branchesEQ l' ls')
        same whom gs | (Yes (R (l' :: ls') (b' :: bs'))) | (Yes prf)

          = Yes (R _ (S (b' :: bs') prf))

        same whom gs | (Yes (R (l' :: ls') (b' :: bs'))) | (No msg no)
          = No (NotAllSame (l'::ls'))
               (\case (R l (S (p :: ps) prf)) =>
                        no $ rewrite sym (funProject p  b') in
                             rewrite sym (funProject ps bs') in prf)

      same whom gs | (No msg no)
        = No msg
             (\case (R x (S projs prf)) => no (R _ projs))

namespace Closed
  export
  project : {w : _} -> {rs : List Role}
         -> {global : Global Nil rs}
         -> (whom : DeBruijn.Role rs w)
         -> (type : Global Nil ts rs ss global)
                 -> DecInfo Projection.Error
                            (Result Nil rs whom global)
  project
    = Projection.project

-}
-- [ EOF ]
