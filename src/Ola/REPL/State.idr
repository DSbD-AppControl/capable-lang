module Ola.REPL.State

import public Data.SortedMap
import public Data.SortedSet

import Toolkit.Data.Location

import Ola.Check.Common

import Ola.Types
import Ola.Core

import Ola.Terms

%default total

public export
data Protocol : Type where
  P : {rs : _}
   -> { type : Global Nil rs}
   -> (Context Ty.Role rs)
   -> (Global.Global Nil ts rs type)
   -> Protocol

public export
data Func = F (Func rs ts s type)


public export
data Ty = T (Ty ts type)

public export
record State where
  constructor S
  file      : Maybe String
  protocols : SortedMap String Protocol
  roles     : SortedMap String Role
  types     : SortedMap String State.Ty
  funcs     : SortedMap String Func
  prog      : Maybe Program

export
defaultState : State
defaultState = S Nothing empty empty empty empty Nothing


export
getProtocol : State -> String -> Ola (Maybe Protocol)
getProtocol st key
  = pure $ lookup key (protocols st)

export
getRole : State -> String -> Ola (Maybe Role)
getRole st key
  = pure $ lookup key (roles st)

-- [ EOF ]
