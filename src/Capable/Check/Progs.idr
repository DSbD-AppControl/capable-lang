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

public export
data Result : (rs    : List Ty.Role)
           -> (ds    : List Ty.Base)
           -> (ss    : List Ty.Session)
           -> (gs    : List Ty.Method)
                    -> Type
  where
    R : (tm   : Prog rs ds ss gs UNIT)
     -> (st   : State)
     -> (p    : PROG)
     -> (eAST : Prog p)
             -> Result rs ds ss gs



check : {p     : PROG}
     -> {rs    : List Ty.Role}
     -> {ds    : List Ty.Base}
     -> {gs    : List Ty.Method}
     -> {ss    : List Ty.Session}
     -> (env   : Env rs ds ss gs Nil)
     -> (state : State)
     -> (prog  : Prog p)
              -> Capable (Result rs ds ss gs)
check env state (Main fc mo)
  = do (state, (FUNC [LIST STR] UNIT ** m)) <- synth state env mo
         | (st, (ty ** _))
             => throwAt fc (MismatchM ty (FUNC [LIST STR] UNIT))

       pure (R (Main m)
               state
               _
               (Main fc mo)
            )

-- [ NOTE ]
--
-- The following should be cleaner, but we have reached the limit of
-- Idris2 inference abilities to reconstruct the raw ast from the
-- projections.
--
-- Well maybe gallais can get it working, but I cannot...

check env state (Def fc DTYPE n val@(TyData fc' UNION _ args) scopeo)
  = do exists fc (delta env) n
       (ty ** tm) <- synth (delta env) val

       let ref = TyVar (MkRef fc' n) R

       let (p ** scope) = generateTags ref args scopeo

       let env   : Env rs (ty::ds) ss gs Nil = { delta $= \c => extend c n ty} env
       let state = { types $= insert n (T tm)} state

       (R scopeTm state _ scope) <- assert_total $ check env state scope

       pure (R (DefType tm scopeTm)
               state
               _
               (Def fc DTYPE n val scope)
            )

check env state (Def fc DTYPE n val@(TyData fc' STRUCT _ (Add a b c d)) scope)
  = do exists fc (delta env) n
       (ty ** tm) <- synth (delta env) val

       let ref = TyVar (MkRef fc' n) R

       let (p ** scope) = generateProjections fc n ref (Add a b c d) scope

       let env   = { delta $= \c => extend c n ty} env
       let state = { types $= insert n (T tm)} state

       R scopeTm state _ scope <- assert_total $ check env state scope

       pure (R (DefType tm scopeTm)
               state
               _
               (Def fc DTYPE n val scope)
            )

check env state (Def fc TYPE n val {rest} scope)
  = do exists fc (delta env) n
       (ty ** tm) <- synth (delta env) val

       let env   = { delta $= \c => extend c n ty} env
       let state = { types $= insert n (T tm)} state

       R scopeTm state _ scope <- check env state scope

       pure (R (DefType tm scopeTm)
               state
               _
               (Def fc TYPE n val scope)
            )

check env state (Def fc FUNC n val scope)
  = do exists fc (gamma env) n

       (state, (FUNC as r ** tm)) <- synth state env val
         | (st, (ty ** _)) => throwAt fc (FunctionExpected ty)

       let env   = Gamma.extend env n (FUNC as r)
       let state = { funcs $= insert n (F tm)} state

       R scopeTm state _ scope <- check env state scope

       pure (R (DefFunc tm scopeTm)
               state
               _
               (Def fc FUNC n val scope)
            )

check env state (Def fc ROLE n val scope)

  = do exists fc (rho env) n
       let env = Rho.extend env n

--       (r ** role) <- synth (rho env) val

       let state = {roles $= insert n (MkRole n)} state

       R scopeTm state _ scope <- check env state scope

       pure (R (DefRole (MkRole n) scopeTm)
               state
               _
               (Def fc ROLE n val scope)
            )


check env state (Def fc PROT n val scope)
  = do maybe (pure ())
             (\_ => throwAt fc (AlreadyBound (MkRef fc n )))
             (!(getProtocol state n))

       (g ** tm) <- synth (delta env) (rho env) (sigma env) val

       prf <- embedAt fc (\((r' ** r),err) => WellFormed "\{reflect (rho env) r} causes error at:\n\{show err}")
                         (wellFormed g)

       let env = Sigma.extend env n (S (rho env) g)

       let state = {protocols $= insert n (P (rho env) g)} state

       R scopeTm state _ scope <- check env state scope

       pure (R (DefProt tm prf scopeTm)
               state
               _
               (Def fc PROT n val scope)
            )

check env state (Def fc SESH n val scope)
  = do exists fc (gamma env) n

       (state, (SESH ctzt whom l as r ** tm)) <- synth state env val
         | (st, (ty ** _)) => throwAt fc (SessionExpected ty)

       let env = Gamma.extend env n (SESH ctzt whom l as r)
       -- @ TODO add sessions to state

       R scopeTm state _ scope <- check env state scope
       pure (R (DefSesh tm scopeTm)
               state
               _
               (Def fc SESH n val scope)
            )

namespace Raw
  export
  check : State -> (r : PROG) -> Capable (Program,State,DPair PROG Prog)
  check st p
    = do let s : State = { file := file st } defaultState
         R p s p' ast <- check empty s (toProg p)
         let s = setProgram p s
         pure (p,s,(p'**ast))



-- [ EOF ]
