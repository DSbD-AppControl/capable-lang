module Capable.Synthesis.LocalVars

import Decidable.Equality

import Data.List.Elem
import Data.List1.Elem
import Data.Vect

import public Data.Singleton


import Toolkit.Data.DList
import Toolkit.Data.DVect
import Toolkit.Data.List.AtIndex
import Toolkit.DeBruijn.Renaming

import public Capable.Bootstrap
import Capable.Types

import Capable.State
import Capable.Check.Common

import Capable.Core

import Capable.Raw.AST
import Capable.Raw.Role
import Capable.Raw.Types
import Capable.Raw.Exprs
import Capable.Terms

public export
data Result : Type where
  R : {e : _} -> Expr e -> Result

export
synthesis : (env  : Env rs ts ps gs ls)
         -> (type : Base)
         -> (str  : String)
                 -> Capable Result
synthesis env type str
  = pure $ maybe (R (Raw.Exprs.Hole (emptyRef str) R))
                 (\n => R (Raw.Exprs.Var (emptyRef n) R))
                 (reflectByValue (lambda env) type)


-- [ EOF ]
