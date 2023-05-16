|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Capable.Types.Protocol.Assignment

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
import public Toolkit.Data.DList.Elem
import Toolkit.Data.DList.All

import public Toolkit.DeBruijn.Renaming


import Capable.Bootstrap
import Capable.Types.Role
import Capable.Types.Base

import Capable.Types.Protocol.Global
import Capable.Types.Protocol.Local.Synth
import Capable.Types.Protocol.Projection

%default total

namespace HasRoles
  mutual
    namespace Protocol
      public export
      data HasRoles : (rs : List Role)
                   -> (lp : Local ks rs)
                   -> (os : Roles rs ss)
                         -> Type
        where
          Crash : HasRoles rs lp Nil
          End   : HasRoles rs lp Nil
          Call  : HasRoles rs lp Nil
          Rec   : HasRoles rs lp os
               -> HasRoles rs (Rec lp) os

          Select : HasRoles rs cont os
                -> Union [whom] os os' prf
                -> HasRoles rs (Select whom label ty prfm cont) os'

          Choice : Branches.HasRoles rs bs os
                -> Union [whom] os os' prf
                -> Protocol.HasRoles rs (Offer whom ty prfm bs) os'

          Choices : HasRoles rs l ls
                 -> HasRoles rs r zs
                 -> Union ls zs os' prf
                 -> Protocol.HasRoles rs (Choices l r) os'

      public export
      data Result : (rs : List Role) -> (p : Local ks rs) -> Type where
        R : {ss : _} -> (os : Roles rs ss) -> Protocol.HasRoles rs lp os -> Result rs lp

    namespace Branch
      public export
      data HasRoles : (rs : List Role)
                   -> (lp : Branch Local ks rs l)
                   -> (os : Roles rs ss)
                         -> Type
        where
          B : Protocol.HasRoles rs        l  os
           ->   Branch.HasRoles rs (B m t l) os

      public export
      data Result : (rs : List Role) -> (p : Branch Local ks rs l) -> Type where
        R : {ss : _} -> (os : Roles rs ss) -> Branch.HasRoles rs lp os -> Result rs lp

    namespace Branches
      public export
      data HasRoles : (rs : List Role)
                   -> (lp : Synth.Branches ks rs lts)
                   -> (os : Roles rs ss)
                         -> Type
        where
          Nil : HasRoles rs Nil Nil

          Add :   Branch.HasRoles rs b os
             -> Branches.HasRoles rs bs os'
             -> Union os os' os'' prf
             -> Branches.HasRoles rs (b::bs) os''

      public export
      data Result : (rs : List Role) -> (p : Synth.Branches ks rs l) -> Type where
        R : {ss : _} -> (os : Roles rs ss) -> Branches.HasRoles rs lp os -> Result rs lp


namespace HasRoles
  mutual
    namespace Protocol
      export
      hasRoles : (p : Local ks rs) -> Protocol.Result rs p
      hasRoles Crash = R [] Crash
      hasRoles End = R [] End
      hasRoles (Call x) = R [] Call
      hasRoles (Rec x)
        = case hasRoles x of
            R _ r => R _ (Rec r)
      hasRoles (Select whom label ty prfM cont)
        = case hasRoles cont of
            R as res => case DList.union [whom] as of
                          (ps ** zs ** prfTy ** prf) => R _ (Select res prf)
      hasRoles (Offer whom type prfM choices)
        = case hasRoles choices of
            R as res => case DList.union [whom] as of
                          (ps ** zs ** prfTy ** prf) => R _ (Choice res prf)

      hasRoles (Choices l r)
        = case hasRoles l of
            R ls lres
              => case hasRoles r of
                   R rz rres
                     => case DList.union ls rz of
                         (ps ** zs ** prfTy ** prf) => R _ (Choices lres rres prf)

    namespace Branch
      export
      hasRoles : (p : Branch Local ks rs l) -> Branch.Result rs p
      hasRoles (B str b cont)
        = case hasRoles cont of
            R _ r => R _ (B r)

    namespace Branches
      export
      hasRoles : (p : Synth.Branches ks rs l) -> Branches.Result rs p
      hasRoles []
        = R _ []
      hasRoles (elem :: rest)
        = case hasRoles elem of
            R a r => case hasRoles rest of
                       R bs rs => case DList.union a bs of
                                   (ps ** zs ** prfTy ** prf) => R _ (Add r rs prf)


namespace UsesRole
  mutual
    namespace Protocol
      public export
      data UsesRole : (rs : List Role)
                   -> (lp : Local ks rs)
                   -> (r  : IsVar rs MkRole)
                         -> Type
        where
          Rec   : UsesRole rs       t  role
               -> UsesRole rs (Rec  t) role

          CHere : (whom : IsVar rs MkRole)
               -> (prf  : whom = role)
                       -> Protocol.UsesRole rs
                                            (Offer whom ty prfm bs)
                                                   role

          SHere : (whom : IsVar rs MkRole)
               -> (prf  : whom = role)
                       -> Protocol.UsesRole rs (Select whom label ty prfM cont)
                                                       role


          SThere : (whom : IsVar rs MkRole)
                -> (prf  : Not (whom = role))
                        -> Protocol.UsesRole rs                            cont  role
                        -> Protocol.UsesRole rs (Select whom label ty prfM cont) role

          CThere : (whom : IsVar rs MkRole)
                -> (prf  : Not (whom = role))
                -> Branches.UsesRole rs                     bs  role
                -> Protocol.UsesRole rs (Offer whom ty prfm bs) role

          LB : UsesRole rs          l    role
            -> UsesRole rs (Choices l r) role

          RB : UsesRole rs            r  role
            -> UsesRole rs (Choices l r) role

    namespace Branch
      public export
      data UsesRole : (rs : List Role)
                   -> (lp : Branch Local ks rs l)
                   -> (r  : IsVar rs MkRole)
                         -> Type
        where
          B : Protocol.UsesRole rs        l  role
           ->   Branch.UsesRole rs (B m t l) role

    namespace Branches
      public export
      data UsesRole : (rs : List Role)
                   -> (lp : Synth.Branches ks rs lts)
                   -> (r  : IsVar rs MkRole)
                          -> Type
        where
          Here :   Branch.UsesRole rs  b      role
              -> Branches.UsesRole rs (b::bs) role

          There : Branches.UsesRole rs             bs  role
               -> Branches.UsesRole rs (B m t l  ::bs) role

namespace UsesRole
  Uninhabited (UsesRole rs Crash role) where
    uninhabited (Rec x) impossible

  Uninhabited (UsesRole rs End role) where
    uninhabited (Rec x) impossible

  Uninhabited (UsesRole rs (Call x) role) where
    uninhabited (Rec x) impossible

  Uninhabited (UsesRole rs Nil role) where
    uninhabited (Here x) impossible
    uninhabited (There x) impossible

namespace UsesRole
  mutual
    namespace Protocol
      export
      usesRole : (lp : Synth.Local ks rs)
              -> (r  : IsVar rs MkRole)
                    -> Dec (UsesRole rs lp r)
      usesRole Crash _
        = No absurd

      usesRole End _
        = No absurd

      usesRole (Call x) _
        = No absurd

      usesRole (Rec x) r with (usesRole x r)
        usesRole (Rec x) r | (Yes prf)
          = Yes (Rec prf)
        usesRole (Rec x) r | (No contra)
          = No $ \case (Rec y) => contra y

      usesRole (Select whom label type p cont) r with (Equality.decEq whom r)
        usesRole (Select whom label type p cont) r | (Yes prf)
          = Yes (SHere whom prf)
        usesRole (Select whom label type p cont) r | (No contra) with (usesRole cont r)
          usesRole (Select whom label type p cont) r | (No contra) | (Yes prf)
            = Yes (SThere whom contra prf)
          usesRole (Select whom label type p cont) r | (No contra) | (No f)
            = No $ \case (SHere whom prf) => contra prf
                         (SThere whom prf y) => f y

      usesRole (Offer whom type p choices) r with (Equality.decEq whom r)
        usesRole (Offer whom type p choices) r | (Yes prf)
           = Yes (CHere whom prf)
        usesRole (Offer whom type p choices) r | (No contra) with (usesRole choices r)
          usesRole (Offer whom type p choices) r | (No contra) | (Yes prf)
            = Yes (CThere whom contra prf)
          usesRole (Offer whom type p choices) r | (No contra) | (No f)
            = No $ \case (CHere whom prf) => contra prf
                         (CThere whom prf y) => f y

      usesRole (Choices l r) p with (usesRole l p)
        usesRole (Choices l r) p | (Yes prf)
          = Yes (LB prf)
        usesRole (Choices l r) p | (No contra) with (usesRole r p)
          usesRole (Choices l r) p | (No contra) | (Yes prf)
            = Yes (RB prf)
          usesRole (Choices l r) p | (No contra) | (No f)
            = No (\case (LB x) => contra x
                        (RB x) => f x)

    namespace Branch
      export
      usesRole : (lp : Branch Local ks rs l)
              -> (r  : IsVar rs MkRole)
                     -> Dec (UsesRole rs lp r)
      usesRole (B str b cont) r with (usesRole cont r)
        usesRole (B str b cont) r | (Yes prf)
          = Yes (B prf)
        usesRole (B str b cont) r | (No contra)
          = No $ \case (B x) => contra x

    namespace Branches
      export
      usesRole : (lp : Synth.Branches ks rs lts)
              -> (r  : IsVar rs MkRole)
                    -> Dec (UsesRole rs lp r)
      usesRole [] r
        = No absurd

      usesRole (b :: rest) r with (usesRole b r)
        usesRole (b :: rest) r | (Yes prf)
          = Yes (Here prf)
        usesRole (b :: rest) r | (No contra) with (usesRole rest r)
          usesRole ((B l b cont) :: rest) r | (No contra) | (Yes prf)
            = Yes (There prf)
          usesRole (b :: rest) r | (No contra) | (No f)
            = No $ \case (Here x) => contra x
                         (There x) => f x

-- [ EOF ]
