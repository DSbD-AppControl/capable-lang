||| Type-checker for Programs.
|||
||| Module    : Types.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
module Ola.Check.Progs

import Toolkit.Data.Location

import Ola.Types
import Ola.Core

import Ola.Raw.Types
import Ola.Raw.Types.View
import Ola.Raw.Exprs

import Ola.Raw.Stmts
import Ola.Raw.Funcs
import Ola.Raw.Progs
import Ola.Raw.Progs.View

import Ola.Check.Common

import Ola.Check.Roles
import Ola.Check.Types
import Ola.Check.Exprs
import Ola.Check.Stmts
import Ola.Check.Funcs

import Ola.Terms.Vars
import Ola.Terms.Roles
import Ola.Terms.Types
import Ola.Terms.Exprs
import Ola.Terms.Stmts
import Ola.Terms.Funcs
import Ola.Terms.Progs

%default total


check : {p     : Prog}
     -> {rs    : List Ty.Role}
     -> {ds,gs : List Ty.Base}
     -> (rho   : Context Ty.Role rs)
     -> (delta : Context Ty.Base ds)
     -> (gamma : Context Ty.Base gs)
     -> (prog  : Prog p)
              -> Ola (Prog rs ds gs UNIT)
check rho delta gamma (RoleDef fc ref r scope)
  = do (r ** tm) <- roleCheck rho r
       scope <- check
                  (extend rho (get ref) r)
                  delta
                  gamma
                  scope
       pure (DefRole tm scope)

check rho delta gamma (TypeDef fc ref val scope)
  = do (ty ** tm) <- typeCheck delta val

       scope <- check
                  rho
                  (extend delta (get ref) ty)
                  gamma
                  scope
       pure (DefType tm scope)

check rho delta gamma (FuncDef fc ref f scope)
  = do (FUNC as r ** f) <- funcCheck rho delta gamma f
         | (ty ** _) => throwAt fc (FunctionExpected ty)

       scope <- check
                  rho
                  delta
                  (extend gamma (get ref) (FUNC as r))
                  scope

       tyTm <- typeReflect delta (FUNC as r)
       pure (DefFunc tyTm f scope)


check rho delta gamma (Main fc f)
  = do (FUNC Nil UNIT ** f) <- funcCheck rho delta gamma f
         | (ty ** _) => mismatchAt fc (FUNC Nil UNIT) ty

       pure (Main f)


export
progCheck : (r : Prog) -> Ola Program
progCheck p
  = check Nil Nil Nil (view p)

-- [ EOF ]
