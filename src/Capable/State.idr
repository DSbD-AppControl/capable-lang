module Capable.State

import Data.List
import public Data.SortedMap
import public Data.SortedSet

import Toolkit.Data.Location

import Capable.Check.Common

import Capable.Types
import Capable.Core

import Capable.Terms

%default total
%hide type

public export
data Protocol : Type where
  P : {rs : _}
   -> (Context Ty.Role rs)
   -> (type : Global Nil rs)
   -> (Global.Global Nil ts rs type)
   -> Protocol

public export
data Func = F (Func rs ts ss s type)


public export
data Hole = H (Env rs ts ss gs ls)

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
  holes     : SortedMap String State.Hole
  prog      : Maybe Program

export
defaultState : State
defaultState = S Nothing empty empty empty empty empty Nothing

export
setProgram : Program -> State -> State
setProgram p = { prog := Just p }

export
isHoley : State -> Capable Bool
isHoley = (pure . isNil . SortedMap.toList . holes)

export
getHole : State -> String -> Capable (Maybe Hole)
getHole st key
  = pure $ lookup key (holes st)

export
getProtocol : State -> String -> Capable (Maybe Protocol)
getProtocol st key
  = pure $ lookup key (protocols st)

export
getRole : State -> String -> Capable (Maybe Role)
getRole st key
  = pure $ lookup key (roles st)

-- [ EOF ]
