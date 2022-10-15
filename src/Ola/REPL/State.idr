module Ola.REPL.State

import public Data.SortedMap
import public Data.SortedSet

import Toolkit.Data.Location


import Ola.Types
import Ola.Core

import Ola.Terms

%default total

public export
data Protocol = P (Global ks ts rs type)

public export
data Role = R (Role rs type)

public export
data Func = F (Func rs ts s type)


public export
data Ty = T (Ty ts type)

public export
record State where
  constructor S
  file      : Maybe String
  protocols : SortedMap String Protocol
  roles     : SortedSet String
  types     : SortedMap String State.Ty
  funcs     : SortedMap String Func
  prog      : Maybe Program

export
defaultState : State
defaultState = S Nothing empty empty empty empty Nothing

-- [ EOF ]
