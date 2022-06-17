||| Ola Programmes.
|||
||| Module    : Progs.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
module Ola.Terms.Progs

import Data.List.Elem
import Data.Vect

import Ola.Terms.Types
import Ola.Terms.Vars
import Ola.Terms.Exprs
import Ola.Terms.Stmts
import Ola.Terms.Funcs

%default total

||| A programme is a type-alias, a function definition, and a
||| top-level function.
|||
||| We index with a typing context for type-aliases and the stack to
||| ensure that both are intrinsically well scoped/typed.
public export
data Prog : (types : List Ty)
         -> (stack : List Ty)
         -> (type  : Ty)
                  -> Type
  where
    ||| A Type-Def.
    DefType : {type : Ty}
           -> (tyRef : Ty types type)
           -> (rest  : Prog (type::types) stack UNIT)
                    -> Prog        types  stack UNIT

    ||| A function definition.
    DefFunc : {arg,return : Ty}
           -> (sig  : Ty types (FUNC arg return))
           -> (func : Func types                     stack  (FUNC arg return))
           -> (rest : Prog types (FUNC arg return :: stack)  UNIT)
                   -> Prog types                     stack   UNIT

    ||| The top-level function.
    Main : Stmt types stack UNIT
        -> Prog types stack UNIT


||| A Closed program.
public export
Programme : Type
Programme
  = Prog Nil Nil UNIT

-- [ EOF ]
