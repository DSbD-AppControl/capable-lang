module Ola.REPL.Load

import Toolkit.Data.Location

import Ola.Types
import Ola.Core

import Ola.Raw.Types
import Ola.Raw.Types.View
import Ola.Raw.Exprs

import Ola.Raw.Stmts
import Ola.Raw.Funcs
import Ola.Raw.Roles
import Ola.Raw.Progs
import Ola.Raw.Progs.View

import Ola.Lexer
import Ola.Parser

import Ola.Check.Common
import Ola.Check.Roles
import Ola.Check.Types
import Ola.Check.Roles
import Ola.Check.Protocols
import Ola.Check.Exprs
import Ola.Check.Stmts
import Ola.Check.Funcs

import Ola.Terms

import Ola.REPL.State

%default total

check : {p     : Prog}
     -> {rs    : List Ty.Role}
     -> {ds,gs : List Ty.Base}
     -> (rho   : Context Ty.Role rs)
     -> (delta : Context Ty.Base ds)
     -> (gamma : Context Ty.Base gs)
     -> (state : State)
     -> (prog  : Prog p)
              -> Ola (Prog rs ds gs UNIT, State)

check rho delta gamma st (SeshDef fc ref s scope)
  = do (g ** tm) <- protocolCheck delta rho s

       (scope,st) <- check
                       rho
                       delta
                       gamma
                       ({protocols $= insert (get ref) (P rho tm)} st)
                       scope
       pure (DefSesh tm scope, st)

check rho delta gamma st (RoleDef fc ref scope)
  = do let rho = (extend rho (get ref) MkRole)
       (MkRole ** role) <- roleCheck rho (RoleRef ref)
       (scope, st) <- check
                       rho
                       delta
                       gamma
                       ({roles $= insert (get ref) (R (role))} st)
                       scope
       pure (DefRole scope, st)


check rho delta gamma st (TypeDef fc ref val scope)
  = do (ty ** tm) <- typeCheck delta val

       (scope, st) <- check
                        rho
                        (extend delta (get ref) ty)
                        gamma
                        ({ types $= insert (get ref) (T tm)} st)
                        scope
       pure (DefType tm scope, st)

check rho delta gamma st (FuncDef fc ref f scope)
  = do (FUNC as r ** f) <- funcCheck rho delta gamma f
         | (ty ** _) => throwAt fc (FunctionExpected ty)

       (scope, st) <- check
                        rho
                        delta
                        (extend gamma (get ref) (FUNC as r))
                        ({funcs $= insert (get ref) (F f)} st)
                        scope

       tyTm <- typeReflect delta (FUNC as r)
       pure (DefFunc tyTm f scope, st)


check rho delta gamma st (Main fc f)
  = do (FUNC Nil UNIT ** f) <- funcCheck rho delta gamma f
         | (ty ** _) => mismatchAt fc (FUNC Nil UNIT) ty

       pure (Main f, st)


checkProg : (r : Prog) -> Ola State
checkProg p
  = do (p,st) <- check Nil Nil Nil defaultState (view p)
       pure ({prog := Just p} st)

export
load : String -> Ola State
load fname
  = do ast <- fromFile fname
       putStrLn "# Finished Parsing"

       st <- checkProg ast
       putStrLn "# Finished Type Checking"

       pure st
-- [ EOF ]
