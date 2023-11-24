module Capable.Synthesis.Terms

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

import Capable.Raw.Expr

export
synthesis : (env : Env rs ts ps gs ls)
         -> (ty  : Base)
                -> Expr rs ts ps gs ls ty
synthesis env CHAR = ?synthesis_rhs_0
synthesis env STR = ?synthesis_rhs_1
synthesis env INT = ?synthesis_rhs_2
synthesis env BOOL = ?synthesis_rhs_3
synthesis env UNIT = ?synthesis_rhs_4
synthesis env (HANDLE x) = ?synthesis_rhs_5
synthesis env (REF x) = ?synthesis_rhs_6
synthesis env (VECTOR x k) = ?synthesis_rhs_7
synthesis env (LIST x) = ?synthesis_rhs_8
synthesis env (TUPLE fields) = ?synthesis_rhs_9
synthesis env (RECORD fields) = ?synthesis_rhs_10
synthesis env (UNION fields) = ?synthesis_rhs_11

-- [ EOF ]
