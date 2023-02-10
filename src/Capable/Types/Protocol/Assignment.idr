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

import Capable.Types.Protocol
import Capable.Types.Protocol.Projection

%default total

public export
Roles : (rs : List Role) -> (ss : List Role) -> Type
Roles rs
  = DList Role (IsVar rs)


namespace HasRoles
  mutual
    namespace Protocol
      public export
      data HasRoles : (rs : List Role)
                   -> (lp : Local ks rs)
                   -> (os : Roles rs ss)
                         -> Type
        where
          Crash : HasRoles rs lp os
          End   : HasRoles rs lp os
          Call  : HasRoles rs lp os
          Rec   : HasRoles rs lp os
               -> HasRoles rs lp os
          Choice : Branches.HasRoles rs bs os
                -> Union [whom] os os' prf
                -> Protocol.HasRoles rs (Choice kind whom ty prfm bs) os'

    namespace Branch
      public export
      data HasRoles : (rs : List Role)
                   -> (lp : Branch Local ks rs l)
                   -> (os : Roles rs ss)
                         -> Type
        where
          B : Protocol.HasRoles rs        l  os
           ->   Branch.HasRoles rs (B m t l) os

    namespace Branches
      public export
      data HasRoles : (rs : List Role)
                   -> (lp : Local.Branches ks rs lts)
                   -> (os : Roles rs ss)
                         -> Type
        where
          Nil : HasRoles rs Nil Nil

          Add :   Branch.HasRoles rs b os
             -> Branches.HasRoles rs bs os'
             -> Union os os' os'' prf
             -> Branches.HasRoles rs (b::bs) os''


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
                                            (Choice kind whom ty prfm bs) role

          CThere : (whom : IsVar rs MkRole)
                -> (prf  : Not (whom = role))
                -> Branches.UsesRole rs                           bs  role
                -> Protocol.UsesRole rs (Choice kind whom ty prfm bs) role

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
                   -> (lp : Local.Branches ks rs lts)
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
      usesRole : (lp : Local ks rs)
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

      usesRole (Choice kind whom type p choices) r with (Equality.decEq whom r)
        usesRole (Choice kind whom type p choices) r | (Yes prf)
          = Yes (CHere whom prf)
        usesRole (Choice kind whom type p choices) r | (No contra) with (usesRole choices r)
          usesRole (Choice kind whom type p choices) r | (No contra) | (Yes prf)
            = Yes (CThere whom contra prf)
          usesRole (Choice kind whom type p choices) r | (No contra) | (No f)
            = No $ \case (CHere whom prf) => contra prf
                         (CThere whom prf y) => f y

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
      usesRole : (lp : Local.Branches ks rs lts)
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
