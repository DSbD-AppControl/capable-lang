|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Capable.Types.Protocol.Global.WellFormed

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
import Capable.Error
import Capable.Types.Role
import Capable.Types.Base

import Capable.Types.Protocol.Global
import Capable.Types.Protocol.Global.HasRoles
import Capable.Types.Protocol.Global.UsesRole
import Capable.Types.Protocol.Local
import Capable.Types.Protocol.Projection

import Capable.Types.Protocol.Global.Projectable

%default total



public export
data WellFormed : (rs : List Role)
               -> (lp : Global Nil rs)
                     -> Type
  where
    WF : {os : Roles rs ss} -> Protocol.HasRoles rs g os
      -> ProjAll rs g os
      -> WellFormed rs g


||| Is the global type well formed.
|||
||| That is, given the global type g.
|||
||| + can all roles in g project g.
|||
||| @TODO Need a better decision procedure...
export
wellFormed : {rs : _}
          -> (g  : Global Nil rs)
                -> Either (DPair Role (Role rs),Projection.Error)
                          (WellFormed rs g)
wellFormed g with (hasRoles g)
  wellFormed g | (R os prf) with (projectable os g)
    wellFormed g | (R os prf) | (Yes prfWhy)
      = Right (WF prf prfWhy)
    wellFormed g | (R os prf) | (No msg no)
      = Left msg


-- [ EOF ]
