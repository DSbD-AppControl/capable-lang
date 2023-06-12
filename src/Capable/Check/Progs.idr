||| Type-checker for Programs.
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Capable.Check.Progs

import Data.List.Views
import Data.String

import Toolkit.Data.Location

import Capable.Types
import Capable.Core

import Capable.Types.Protocol.Global.WellFormed

import Capable.Raw.AST
import Capable.Raw.Types
import Capable.Raw.DTypes
import Capable.Raw.Exprs
import Capable.Raw.Funcs
import Capable.Raw.Role
import Capable.Raw.Progs

import Capable.Check.Common
import Capable.Check.Elab
import Capable.Check.Types
import Capable.Check.DataTypes
import Capable.Check.Roles
import Capable.Check.Protocols
import Capable.Check.Exprs
import Capable.Check.Funcs
import Capable.Check.Sessions

import Capable.Terms.Vars
import Capable.Terms.Roles
import Capable.Terms.Protocols
import Capable.Terms.Sessions
import Capable.Terms.Types
import Capable.Terms.Exprs
import Capable.Terms.Funcs
import Capable.Terms.Progs

import Capable.State

%default total
%hide fields


check : {p     : PROG}
     -> {rs    : List Ty.Role}
     -> {ds    : List Ty.Base}
     -> {gs    : List Ty.Method}
     -> {ss    : List Ty.Session}
     -> (env   : Env rs ds ss gs Nil)
     -> (state : State)
     -> (prog  : Prog p)
              -> Capable (Prog rs ds ss gs UNIT, State)
check env state (Main fc m)
  = do (FUNC [LIST STR] UNIT ** m) <- synth env m
         | (ty ** _)
             => throwAt fc (MismatchM ty (FUNC [LIST STR] UNIT))

       pure (Main m, state)

-- [ NOTE ]
--
-- The following should be cleaner, but we have reached the limit of
-- Idris2 inference abilities to reconstruct the raw ast from the
-- projections.
--
-- Well maybe gallais can get it working, but I cannot...

check env state (Def fc DTYPE n val@(TyData fc' UNION _ args) scope)
  = do exists fc (delta env) n
       (ty ** tm) <- synth (delta env) val

       let val = TyVar (MkRef fc' n) R

       let (p ** scope) = generateTags val args scope

       let env   = { delta $= \c => extend c n ty} env
       let state = { types $= insert n (T tm)} state

       (scope, state) <- assert_total $ check env state scope

       pure (DefType tm scope, state)

check env state (Def fc DTYPE n val@(TyData fc' STRUCT _ (Add a b c d)) scope)
  = do exists fc (delta env) n
       (ty ** tm) <- synth (delta env) val

       let val = TyVar (MkRef fc' n) R
       let (p ** scope) = generateProjections fc n val (Add a b c d) scope

       let env   = { delta $= \c => extend c n ty} env
       let state = { types $= insert n (T tm)} state

       (scope, state) <- assert_total $ check env state scope

       pure (DefType tm scope, state)

check env state (Def fc TYPE n val {rest} scope)
  = do exists fc (delta env) n
       (ty ** tm) <- synth (delta env) val

       let env   = { delta $= \c => extend c n ty} env
       let state = { types $= insert n (T tm)} state

       (scope, state) <- check env state scope

       pure (DefType tm scope, state)

check env state (Def fc FUNC n val scope)
  = do exists fc (gamma env) n

       (FUNC as r ** tm) <- synth env val
         | (ty ** _) => throwAt fc (FunctionExpected ty)

       let env   = Gamma.extend env n (FUNC as r)
       let state = { funcs $= insert n (F tm)} state

       (scope, state) <- check env state scope

       pure (DefFunc tm scope, state)

check env state (Def fc ROLE n val scope)

  = do exists fc (rho env) n
       let env = Rho.extend env n

--       (r ** role) <- synth (rho env) val

       let state = {roles $= insert n (MkRole n)} state

       (scope, state) <- check env state scope

       pure (DefRole (MkRole n) scope, state)


check env state (Def fc PROT n val scope)
  = do maybe (pure ())
             (\_ => throwAt fc (AlreadyBound (MkRef fc n )))
             (!(getProtocol state n))

       (g ** tm) <- synth (delta env) (rho env) val

       prf <- embedAt fc (\((r' ** r),err) => WellFormed "\{reflect (rho env) r} causes:\n\{show err}")
                         (wellFormed g)

       let env = Sigma.extend env n (S (rho env) g)

       let state = {protocols $= insert n (P (rho env) g tm)} state

       (scope, state) <- check env state scope

       pure (DefProt tm prf scope, state)

check env state (Def fc SESH n val scope)
  = do exists fc (gamma env) n

       (SESH ctzt whom l as r ** tm) <- synth env val
         | (ty ** _) => throwAt fc (SessionExpected ty)

       let env = Gamma.extend env n (SESH ctzt whom l as r)
       -- @ TODO add sessions to state

       (scope, state) <- check env state scope
       pure (DefSesh tm scope, state)

namespace Raw
  export
  check : (r : PROG) -> Capable (Program,State)
  check p
    = check empty defaultState (toProg p)



-- [ EOF ]
