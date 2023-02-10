|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Capable.Types.Protocol.Selection

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

public export
data Select : (this : Branch Local ks rs (l,t))
           -> (prf  : Marshable (l,t))
           -> (from : DList (String,Base)
                            (Branch Local ks rs)
                            (field::fs))
           -> (prfM : DList (String,Base)
                            Marshable
                            (field::fs))
                   -> Type
  where
    Here :  Select b f (b::bs) (f::fs)
    There : Select b f      bs       fs
         -> Select b f (b'::bs) (f'::fs)


-- [ EOF ]
