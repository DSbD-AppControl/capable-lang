|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Capable.Types.Protocol.Global.HasRoles

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
--import Capable.Types.Protocol.Global.HasRoles
import Capable.Types.Protocol.Local
import Capable.Types.Protocol.Projection

%default total


mutual
  namespace Protocol
    public export
    data HasRoles : (rs : List Role)
                 -> (lp : Global ks rs)
                 -> (os : Roles rs ss)
                       -> Type
      where
        End   : HasRoles rs lp Nil
        Call  : HasRoles rs lp Nil
        Rec   : HasRoles rs lp os
             -> HasRoles rs (Rec lp) os

        Choice : Branches.HasRoles rs bs os
              -> Union [s,r]             os os' prf
              -> Protocol.HasRoles rs (Choice s r ty prfm notsr bs)
                                      os'

    public export
    data Result : (rs : List Role)
               -> (p  : Global ks rs)
                     -> Type where
      R : {ss  : _}
       -> (os  : Roles rs ss)
       -> (res : Protocol.HasRoles rs lp os)
              -> Result rs lp

  namespace Branch
    public export
    data HasRoles : (rs : List Role)
                 -> (lp : Branch Global ks rs l)
                 -> (os : Roles rs ss)
                       -> Type
      where
        B : Protocol.HasRoles rs        l  os
         ->   Branch.HasRoles rs (B m t l) os

    public export
    data Result : (rs : List Role)
               -> (p  : Branch Global ks rs l)
                     -> Type
      where
        R : {ss  : _}
         -> (os  : Roles rs ss)
         -> (res : Branch.HasRoles rs lp os)
                -> Result rs lp

  namespace Branches
    public export
    data HasRoles : (rs : List Role)
                 -> (lp : Global.Branches ks rs lts)
                 -> (os : Roles rs ss)
                       -> Type
      where
        Nil : HasRoles rs Nil Nil

        Add :   Branch.HasRoles rs b os
           -> Branches.HasRoles rs bs os'
           -> Union os os' os'' prf
           -> Branches.HasRoles rs
                                (b::bs)
                                os''

    public export
    data Result : (rs : List Role)
               -> (p  : Global.Branches ks rs l)
                     -> Type where
      R : {ss : _}
       -> (os : Roles rs ss)
       -> Branches.HasRoles rs lp os
       -> Result rs lp


mutual
  namespace Protocol
    export
    hasRoles : (p : Global ks rs) -> Protocol.Result rs p

    hasRoles End = R [] End
    hasRoles (Call x) = R [] End
    hasRoles (Rec x)
      = case hasRoles x of
        R _ r => R _ (Rec r)

    hasRoles (Choice s r type prfM prfR opties)
      = case hasRoles opties of
          R os pO =>
            case DList.union [s,r] os of
              (ps ** zs ** prfTy ** prf) => R _ (Choice pO prf)

  namespace Branch
    export
    hasRoles : (p : Branch Global ks rs l) -> Branch.Result rs p
    hasRoles (B str b cont)
      = case hasRoles cont of
          R _ r => R _ (B r)

  namespace Branches
    export
    hasRoles : (p : Global.Branches ks rs l) -> Branches.Result rs p
    hasRoles []
      = R _ []
    hasRoles (elem :: rest)
      = case hasRoles elem of
          R a r => case hasRoles rest of
                     R bs rs => case DList.union a bs of
                                 (ps ** zs ** prfTy ** prf) => R _ (Add r rs prf)


-- [ EOF ]
