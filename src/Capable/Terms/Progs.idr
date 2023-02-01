||| Capable Programmes.
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Capable.Terms.Progs

import Data.List.Elem
import Data.Vect

import Capable.Types.Protocol.Projection

import Capable.Terms.Vars
import Capable.Terms.Roles
import Capable.Terms.Types
import Capable.Terms.Protocols
import Capable.Terms.Protocols.Projection
import Capable.Terms.Exprs
import Capable.Terms.Funcs
import Capable.Terms.Sessions

%default total
-- @TODO remove functions from base...

||| A programme is a role-def, type-def, a function-def, or a
||| top-level main function.
|||
||| We index with various contexts that weare intrinsically well
||| scoped/typed.
public export
data Prog : (roles   : List Ty.Role)
         -> (types   : List Ty.Base)
         -> (globals : List Ty.Session)
         -> (stack   : List Ty.Method)
         -> (type    :      Ty.Base)
                  -> Type
  where
    DefProt : (prot  : Global Nil types roles g)
           -> (scope : Prog roles types (S g::globals) stack UNIT)
                    -> Prog roles types       globals  stack UNIT

    DefRole : (rest : Prog (MkRole::roles) types globals stack UNIT)
                   -> Prog          roles  types globals stack UNIT

    ||| A Type-Def.
    DefType : {type : Ty.Base}
           -> (tyRef : Ty types type)
           -> (rest  : Prog roles (type::types) globals stack UNIT)
                    -> Prog roles        types  globals stack UNIT

    ||| A function definition.
    DefFunc : {args   : List Ty.Base}
           -> {return : Ty.Base}
--           -> (sig    : Ty types (FUNC args return))
           -> (func   : Func roles types globals                      stack   (FUNC args return))
           -> (rest   : Prog roles types globals (FUNC args return :: stack)  UNIT)
                     -> Prog roles types globals                      stack   UNIT

    ||| A session definition.
    DefSesh : {args   : List Ty.Base}
           -> {return : Ty.Base}
           -> {l      : Local Nil roles}
           -> (proto  : IsVar globals (S global))
           -> (whom   : IsVar roles   MkRole)
           -> (prf    : Project Nil roles whom global l)
           -> (sesh   : Session roles types globals                             stack   (SESH whom l args return))
           -> (rest   : Prog    roles types globals (SESH whom l args return :: stack)  UNIT)
                     -> Prog    roles types globals                             stack   UNIT

    ||| The top-level function.
    ||| @TODO change return to INT...
    Main : Func roles types globals stack (FUNC Nil UNIT)
        -> Prog roles types globals stack           UNIT


||| A Closed program.
public export
Program : Type
Program
  = Prog Nil Nil Nil Nil UNIT

-- [ EOF ]
