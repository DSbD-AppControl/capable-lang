|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Capable.Types.Protocol.Global.UsesRole

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
import Capable.Types.Protocol.Global.HasRoles
import Capable.Types.Protocol.Local
import Capable.Types.Protocol.Projection

%default total

mutual
  namespace Protocol
    public export
    data UsesRole : (rs : List Role)
                 -> (lp : Global ks rs)
                 -> (o  : Role rs u)
                       -> Type
      where
        RLater : UsesRole rs      lp  o
              -> UsesRole rs (Rec lp) o

        Sender : Protocol.UsesRole rs (Choice s r ty p nsr bs) s

        Receiver : Protocol.UsesRole rs (Choice s r ty p nsr bs) r

        CLater : Branches.UsesRole rs                           bs  o
              -> Protocol.UsesRole rs (Choice s r ty prfm notsr bs) o


  namespace Branch
    public export
    data UsesRole : (rs : List Role)
                 -> (lp : Branch Global ks rs l)
                 -> (o  : Role rs u)
                       -> Type
      where
        B : Protocol.UsesRole rs        l  o
         ->   Branch.UsesRole rs (B m t l) o


  namespace Branches
    public export
    data UsesRole : (rs : List Role)
                 -> (lp : Global.Branches ks rs lts)
                 -> (o  : Role rs u)
                       -> Type
      where
        Nil : UsesRole rs Nil o

        Add :   Branch.UsesRole rs  b      o
           -> Branches.UsesRole rs     bs  o
           -> Branches.UsesRole rs (b::bs) o


public export
data UsesRoles : (rs : List Role)
              -> (lp : Global ks rs)
              -> (os : Roles rs ss)
                    -> Type
  where
    Nil : UsesRoles rs lp Nil
    (::) : UsesRole  rs lp o
        -> UsesRoles rs lp os
        -> UsesRoles rs lp (o::os)


-- [ EOF ]
