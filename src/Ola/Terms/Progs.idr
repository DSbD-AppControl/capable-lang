||| Ola Programmes.
|||
||| Module    : Progs.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
module Ola.Terms.Progs

import Data.List.Elem
import Data.Vect

import Ola.Terms.Vars
import Ola.Terms.Roles
import Ola.Terms.Types
import Ola.Terms.Exprs
import Ola.Terms.Stmts
import Ola.Terms.Funcs

%default total

||| A programme is a role-def, type-def, a function-def, or a
||| top-level main function.
|||
||| We index with various contexts that weare intrinsically well
||| scoped/typed.
public export
data Prog : (roles : List Ty.Role)
         -> (types : List Ty.Base)
         -> (stack : List Ty.Base)
         -> (type  :      Ty.Base)
                  -> Type
  where
    DefRole : (rest : Prog (MkRole::roles) types stack UNIT)
                   -> Prog          roles  types stack UNIT
    ||| A RoleDef Synon,
    DefRoleSyn : (roleRef : Role roles MkRole)
              -> (rest    : Prog roles types stack UNIT)
                         -> Prog roles  types stack UNIT
    ||| A Type-Def.
    DefType : {type : Ty.Base}
           -> (tyRef : Ty types type)
           -> (rest  : Prog roles (type::types) stack UNIT)
                    -> Prog roles        types  stack UNIT

    ||| A function definition.
    DefFunc : {args   : List Ty.Base}
           -> {return : Ty.Base}
           -> (sig    : Ty types (FUNC args return))
           -> (func   : Func roles types                      stack   (FUNC args return))
           -> (rest   : Prog roles types (FUNC args return :: stack)  UNIT)
                     -> Prog roles types                      stack   UNIT


    ||| The top-level function.
    ||| @TODO change return to INT...
    Main : Func roles types stack (FUNC Nil UNIT)
        -> Prog roles types stack           UNIT


||| A Closed program.
public export
Program : Type
Program
  = Prog Nil Nil Nil UNIT

-- [ EOF ]
