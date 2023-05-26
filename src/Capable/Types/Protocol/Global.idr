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
data Global : List Kind -> List Role -> Type where
  End : Global ks rs

  Call : {v,vs : _} -> RecVar vs v -> Global vs rs

  Rec : (v : Kind)
     -> Global (v::vs) rs
     -> Global     vs  rs

  Choice : {x,y, fs : _}
        -> (s : Role rs x)
        -> (r : Role rs y)
        -> (type   : Singleton (UNION (field:::fs)))
        -> (prfM   : Marshable (UNION (field:::fs)))
        -> (prfR   : Not (REquals rs s r))
        -> (opties : DList (String,Base)
                           (Branch Global ks rs)
                           (field::fs))
                  -> Global ks rs



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
