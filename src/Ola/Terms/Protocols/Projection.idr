||| Types as terms because we want to mirror real programmes.
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Ola.Terms.Protocols.Projection

import Decidable.Equality
import Toolkit.Decidable.Informative
import Toolkit.Decidable.Equality.Indexed

import Data.Singleton
import public Data.List.Elem
import public Data.List.Quantifiers

import public Data.List1
import public Data.List1.Quantifiers

import public Toolkit.Data.DList


import public Ola.Types
import public Ola.Types.Role
import        Ola.Terms.Vars
import        Ola.Terms.Roles
import        Ola.Terms.Types
import        Ola.Terms.Protocols

%default total

public export
data Result : (ks : List Kind)
           -> (rs : List Role)
           -> (whom : Role rs MkRole)
           -> (global : Global ks rs)
                     -> Type
  where
    R :  (local : Local ks rs)
      -> (proj  : Protocol.Project ks rs whom global local)
               -> Result ks rs whom global
namespace Branch
  public export
  data Result : (ks : List Kind)
             -> (rs : List Role)
             -> (whom   : Role rs MkRole)
             -> (global : Global.Branch ks rs)
                       -> Type
    where
      R : (l : Local.Branch ks rs)
       -> (proj : Branch.Project ks rs whom g l) -> Result ks rs whom g

namespace Branches
  public export
  data Result : (ks : List Kind)
             -> (rs : List Role)
             -> (whom   : Role rs MkRole)
             -> (global : Global.Branches ks rs)
                       -> Type
    where
      R : (local : Local.Branches ks rs)
       -> (proj  : List.Project ks rs whom global local)
                -> Result ks rs whom global

namespace Branches1
  public export
  data Result1 : (ks : List Kind)
              -> (rs : List Role)
              -> (whom   : Role rs MkRole)
              -> (global : Global.Branches1 ks rs)
                       -> Type
    where
      R1 : (local : Local.Branches1 ks rs)
        -> (proj  : List1.Project ks rs whom global local)
                 -> Result1 ks rs whom global


  namespace Same
    public export
    data Result : (ks : List Kind)
               -> (rs : List Role)
               -> (whom   : Role rs MkRole)
               -> (global : Global.Branches1 ks rs)
                         -> Type
      where
        R : (l : _) -> (proj : Same1 ks rs whom gs l) -> Result ks rs whom gs

{-
se (BSEQ Refl) => ?as_1)

equivs pa (Next proj ltr)
   = ?equivs_rhs_1
-}

mutual

  export
  project : {rs : List Role}
         -> {0 global : Global ks rs}
         -> (whom : Role rs MkRole)
         -> (type : Global ks ts rs global)
                 -> DecInfo () -- TODO
                            (Result ks rs whom global)

  project whom End
    = Yes (R _ End)

  project whom (Call prf)
    = Yes (R _ Call)

  project whom (Rec type) with (project whom type)
    project whom (Rec type) | (Yes (R l proj))
      = Yes (R _ (Rec proj))

    project whom (Rec type) | (No msg no)
      = No () -- TODO
           (\(R (Rec a) (Rec this)) => no (R a this))

  project whom (Choice s r noSR cs) with (involved whom s r noSR)
    -- [ NOTE ] Sending
    project s (Choice s r noSR cs) | (Sends Refl) with (Branches1.project s cs)
      project s (Choice s r noSR cs) | (Sends Refl) | (Yes (R1 l proj))
        = Yes (R _ (Select (Same Refl Refl) proj))
      project s (Choice s r noSR cs) | (Sends Refl) | (No msg no)
        = No () -- TODO
             (\case (R _ (Select prf bs))       => no (R1 _ bs)
                    (R _ (Offer prf bs))        => no (R1 _ bs)
                    (R _ (Merge prfS prfR prf)) => prfS (Same Refl Refl)
             )

    -- [ NOTE ] Receiving
    project r (Choice s r noSR cs) | (Recvs Refl) with (Branches1.project r cs)
      project r (Choice s r noSR cs) | (Recvs Refl) | (Yes (R1 l proj))
        = Yes (R _ (Offer (Same Refl Refl) proj))
      project r (Choice s r noSR cs) | (Recvs Refl) | (No msg no)
        = No () -- TODO
             (\case (R _ (Select prf bs)) => no (R1 _ bs)
                    (R _ (Offer prf bs)) => no (R1 _ bs)
                    (R _ (Merge prfS prfR prf)) => prfR (Same Refl Refl)
             )


    -- [ NOTE ] Not involved
    project whom (Choice s r noSR cs) | (Skips sNot rNot) with (same1 whom cs)
      project whom (Choice s r noSR (Bs1 bs)) | (Skips sNot rNot) | (Yes (R (B l t c) (S1 projs prf)))
        = Yes (R _ (Merge sNot rNot (S1 projs prf)))
      project whom (Choice s r noSR cs) | (Skips sNot rNot) | (No msg no)
        = No ()
             (\case (R _ (Select prf bs)) => sNot prf
                    (R _ (Offer prf bs)) => rNot prf
                    (R _ (Merge prfS prfR (S1 projs prfs))) => no (R _ (S1 projs prfs))
             )

  namespace Branch
    export
    project : {rs : _}
           -> (whom : Role rs MkRole)
           -> {0 g  : Global.Branch ks rs}
           -> (type : Branch ks ts rs g)
                   -> DecInfo ()
                              (Branch.Result ks rs whom g)
    project whom (B label type choice) with (project whom choice)
      project whom (B label type choice) | (Yes (R local proj))
        = Yes (R _ (B label _ proj))
      project whom (B label type choice) | (No msg no)
        = No () (\case (R (B label t l) (B label t x)) => no (R l x))

  namespace Branches
    export
    project : {rs : _}
           -> (whom   : Role rs MkRole)
           -> {0  bs : Global.Branches ks rs}
           -> (type   : Branches ks ts rs bs)
                     -> DecInfo () -- TODO
                                (Branches.Result ks rs whom bs)

    project whom []
      = Yes (R _ [])
    project whom (b :: x) with (project whom b)
      project whom (b :: x) | (Yes (R lb proj)) with (Branches.project whom x)
        project whom (b :: x) | (Yes (R lb proj)) | (Yes (R l y))
          = Yes (R _ (proj :: y))
        project whom (b :: x) | (Yes (R lb proj)) | (No msg no)
          = No () -- TODO
               (\case (R _ (y :: z)) => no (R _ z))

      project whom (b :: x) | (No msg no)
        = No () -- TODO
             (\case (R _ ((B _ _ y) :: z)) => no (R _ (B _ _ y)))

  namespace Branches1
    export
    project : {rs : _}
           -> (whom   : Role rs MkRole)
           -> { 0 bs : Global.Branches1 ks rs}
           -> (type   : Branches1 ks ts rs bs)
                     -> DecInfo () -- TODO
                                (Branches1.Result1 ks rs whom bs)

    project whom (Bs1 x) with (Branches.project whom x)
      project whom (Bs1 x) | (Yes (R _ (y :: z)))
        = Yes (R1 _ (Proj (y :: z)))
      project whom (Bs1 x) | (No msg no)
        = No () -- TODO
             (\case (R1 _ (Proj y)) => no (R _ y))

  namespace Same

    helper : {b' : Global.Branch ks rs}
          -> {bs' : Global.Branches ks rs}
          -> (y  : Branch.Project ks rs whom b'  yt)
          -> (ys : List.Project ks rs whom bs' yts)
          -> (no : All (Equal yt) yts -> Void)
          -> Same1 ks rs whom (b' ::: bs') yt
          -> Void

    export
    same1 : {rs   : _}
         -> {0 bs : Global.Branches1 ks rs}
         -> (whom : Role rs MkRole)
         -> (gs   : Branches1 ks ts rs bs)
                 -> DecInfo ()
                           (Same.Result ks rs whom bs)
    same1 whom (Bs1 x) with (Branches.project whom x)
      same1 whom (Bs1 x) | (Yes (R (yt :: yts) (y :: ys))) with (branchesEq yt yts)
        same1 whom (Bs1 x) | (Yes (R (yt :: yts) (y :: ys))) | (Yes prfWhy)
          = Yes (R _ (S1 (Proj (y :: ys)) prfWhy))
        same1 whom (Bs1 x) | (Yes (R (yt :: yts) (y :: ys))) | (No msg no)
          = No () $ \case (R l (S1 (Proj (p :: ps)) prf)) =>
                           no $ rewrite sym (funProject p y) in
                                rewrite sym (funProject ps ys) in
                                prf
      same1 whom (Bs1 x) | (No msg no)
        = No () (\case (R _ (S1 (Proj y) prf)) => no (R _ y))

-- [ EOF ]
