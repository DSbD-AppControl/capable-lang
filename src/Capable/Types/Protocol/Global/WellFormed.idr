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

%default total

namespace WellFormed

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

  project : {rs : _}
         -> (os : Roles     rs ss)
         -> ( g : Global Nil rs)
               -> DecInfo (Role rs,Projection.Error)
                          (ProjAll rs g os)
  project {ss = []} [] g
    = Yes End
  project {ss = (MkRole :: xs)} (elem :: rest) g
    = case Closed.project elem g of
        Yes (l ** p) =>
          case WellFormed.project rest g of
            Yes ps => Yes (Ext p ps)
            No msg no
              => No msg
                    (\case (Ext x y) => no y)
        No msg no =>
          No (elem,msg)
             (\case (Ext {l} x y) => no (l ** x))

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
  ||| @returns The first role that fails projection.
  |||
  ||| @TODO Need a better decision procedure...
  export
  wellFormed : {rs : _}
            -> (g  : Global Nil rs)
                  -> Either (Role rs,Projection.Error)
                            (WellFormed rs g)
  wellFormed g with (hasRoles g)
    wellFormed g | (R os prf) with (project os g)
      wellFormed g | (R os prf) | (Yes prfWhy)
        = Right (WF prf prfWhy)
      wellFormed g | (R os prf) | (No msg no)
        = Left msg


-- [ EOF ]
