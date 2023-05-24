|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Capable.Types.Protocol.Global.Projectable

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

%default total

public export
data ProjAll : (rs : List Role)
            -> (lp : Global Nil rs)
            -> (os : Roles rs ss)
                  -> Type

  where
    End : ProjAll rs lp Nil

    Ext :  {l : _} -> Project Nil rs r g l
        -> ProjAll rs g     os
        -> ProjAll rs g (r::os)

||| Given a list fo roles, can all the roles project the given global type.
|||
||| Fails greedily and returns the first role that fails projection, together with the error message.
|||

export
projectable : {rs : _}
           -> (os : Roles     rs ss)
           -> ( g : Global Nil rs)
                 -> DecInfo (Role rs,Projection.Error)
                            (ProjAll rs g os)
projectable {ss = []} [] g
  = Yes End
projectable {ss = (MkRole :: xs)} (elem :: rest) g
  = case Closed.project elem g of
      Yes (l ** p) =>
        case projectable rest g of
          Yes ps => Yes (Ext p ps)
          No msg no
            => No msg
                  (\case (Ext x y) => no y)
      No msg no =>
        No (elem,msg)
           (\case (Ext {l} x y) => no (l ** x))

-- [ EOF ]
