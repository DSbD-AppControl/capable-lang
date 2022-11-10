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

import Ola.Raw.AST
import Ola.Raw.Types
import Ola.Raw.Exprs

import Ola.Raw.Funcs
import Ola.Raw.Role
import Ola.Raw.Progs
import Ola.Check.Common

import Ola.Check.Types
import Ola.Check.Roles
import Ola.Check.Protocols
import Ola.Check.Exprs
import Ola.Check.Funcs

import Ola.Terms.Vars
import Ola.Terms.Roles
import Ola.Terms.Protocols
import Ola.Terms.Types
import Ola.Terms.Exprs
import Ola.Terms.Funcs
import Ola.Terms.Progs

import Ola.REPL.State

%default total

check : {p     : PROG}
     -> {rs    : List Ty.Role}
     -> {ds,gs : List Ty.Base}
     -> (env   : Env rs ds gs)
     -> (state : State)
     -> (prog  : Prog p)
              -> Ola (Prog rs ds gs UNIT, State)
check env state (Main fc m)
  = do (tyM ** m) <- synth env m

       Refl <- compare fc (FUNC Nil UNIT) tyM

       pure (Main m, state)

check env state (Def fc TYPE n val scope)
  = do (ty ** tm) <- synth (delta env) val

       let env   = { delta $= \c => extend c n ty} env
       let state = { types $= insert n (T tm)} state

       (scope, state) <- check env state scope

       pure (DefType tm scope, state)

check env state (Def fc FUNC n val scope)
  = do (FUNC as r ** tm) <- synth env val
         | (ty ** _) => throwAt fc (FunctionExpected ty)

       let env   = Gamma.extend env n (FUNC as r)
       let state = { funcs $= insert n (F tm)} state

       (scope, state) <- check env state scope

       tyTm <- reflect (delta env) (FUNC as r)

       pure (DefFunc tyTm tm scope, state)

check env state (Def fc ROLE n val scope)

  = do let env = extend env n

       (MkRole ** role) <- synth (rho env) val

       let state = {roles $= insert n (MkRole)} state

       (scope, state) <- check env state scope

       pure (DefRole scope, state)


check env state (Def fc PROT n val scope)
  = do (g ** tm) <- synth (delta env) (rho env) val

       let state = {protocols $= insert n (P (rho env) tm)} state

       (scope, state) <- check env state scope

       pure (DefSesh tm scope, state)


namespace Raw
  export
  check : (r : PROG) -> Ola (Program,State)
  check p
    = check empty defaultState (toProg p)



-- [ EOF ]
