||| Statements one can make in function bodies.
|||
||| Module    : Stmts.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
module Ola.Terms.Stmts

import Data.List.Elem
import Data.Vect

import Ola.Terms.Vars
import Ola.Terms.Types
import Ola.Terms.Exprs

%default total

||| A Statement.
|||
||| We index by both a typing context (for keeping track of typing
||| aliases) and the stack.
public export
data Stmt : (types : List Ty)
         -> (stack : List Ty)
         -> (type  : Ty)
                  -> Type
  where
    ||| Bind things to the stack!
    Let : {type : Ty}
       -> (ty   : Ty   types               type)
       -> (expr : Expr types        stack  type)
       -> (rest : Stmt types (type::stack) return)
               -> Stmt types        stack  return

    ||| Run an expression that return's nothing, and then continue.
    |||
    ||| We use this to capture function calls & mutations as
    ||| statements.
    Seq : (this    : Expr types stack UNIT)
       -> (notThis : Stmt types stack body)
                  -> Stmt types stack body

    ||| A statement about binary decisions.
    Cond : (cond : Expr types stack BOOL)
        -> (tt   : Stmt types stack return)
        -> (ff   : Stmt types stack return)
        -> (rest : Stmt types stack return)
                -> Stmt types stack return

    ||| A statement about matching.
    Match : {a,b : Ty}
         -> (expr  : Expr types     stack  (UNION a b))
         -> (left  : Stmt types (a::stack)  return)
         -> (right : Stmt types (b::stack)  return)
         -> (rest  : Stmt types     stack   return)
                  -> Stmt types     stack   return

    ||| A general while loop construct.
    |||
    ||| We will elaborate for, and foreach loops to this.
    ||| We won't support Do nor other loops.
    |||
    ||| Breaking will be supported, but not continue...
    While : (expr : Expr types stack BOOL)
         -> (body : Stmt types stack return)
         -> (rest : Stmt types stack return)
                 -> Stmt types stack return

    ||| A side effect, run.
    Print : (this : Expr types stack STR)
         -> (rest : Stmt types stack return)
                 -> Stmt types stack return

    ||| Return a value.
    Return : (expr : Expr types stack this)
                  -> Stmt types stack this

    ||| End of computation but no value.
    End : Stmt types stack UNIT

-- [ NOTE ]
--
-- TO assist in early return we distinguish between returning Unit and other expressions including Unit.
-- This might not be a good idea, we shall see.

-- [ EOF ]
