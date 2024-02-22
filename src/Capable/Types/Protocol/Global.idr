module Capable.Types.Protocol.Global

import Decidable.Equality
import Data.String

import public Data.Singleton

import Data.List.Elem
import Data.List1
import Data.List.Quantifiers

import Text.PrettyPrint.Prettyprinter
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

import public Capable.Types.Protocol.Common

%default total

public export
Global : List Kind -> List Role -> Type
Global = Protocol GLOBAL

public export
Branches : List Kind -> List Role -> List (String, Base) -> Type
Branches ks rs
  = DList (String, Base)
          (Branch Global ks rs)

namespace Ty
  public export
  data Session : Type where
    S : {rs : _} -> Context Role rs -> Global Nil rs -> Session

-- [ EOF ]
