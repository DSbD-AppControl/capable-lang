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

mutual
  ||| A Statement.
  |||
  ||| We index by both a typing context (for keeping track of typing
  ||| aliases) and the stack.
  public export
  data Stmt : (types : List Ty)
           -> (stackI,stackO : List Ty)
           -> (type  : Ty)
                    -> Type
    where
      ||| Bind things to the stack!
      Let : {type : Ty}
         -> (ty   : Ty   types                     type)
         -> (expr : Expr types          stack      type)
         -> (rest : Stmt types (type :: stack) out return)
                 -> Stmt types          stack  out return

      |||
      Mutate : {type  : Ty}
            -> (loc   : Expr types stack      (REF type))
            -> (value : Expr types stack           type)
            -> (rest  : Stmt types stack out  return)
                     -> Stmt types stack out  return

      ||| Run a, possibly, side-effecting computation, and carry on.
      |||
      ||| We use this primarily to capture function calls.
      Run : {this : Ty}
         -> (expr : Expr types stack     this)
         -> (rest : Stmt types stack out return)
                 -> Stmt types stack out return

      ||| A statement about binary decisions.
      Cond : (cond : Expr types stack      BOOL)
          -> (tt   : Stmt types stack outA return)
          -> (ff   : Stmt types stack outB return)
          -> (rest : Stmt types stack out  return)
                  -> Stmt types stack out  return

      ||| A statement about matching.
      Match : {a,b : Ty}
           -> (expr  : Expr types     stack        (UNION a b))
           -> (left  : Stmt types (a::stack) outA return)
           -> (right : Stmt types (b::stack) outB return)
           -> (rest  : Stmt types     stack  out  return )
                    -> Stmt types     stack  out  return

      ||| A statement about splitting
      Split : {a,b : Ty}
           -> (expr : Expr types        stack      (PAIR a b))
           -> (body : Stmt types (b::a::stack) out return)
                   -> Stmt types        stack  out return

      ||| A general while loop construct.
      |||
      While : (expr : Expr types stack      BOOL)
           -> (body : Stmt types stack outA return)
           -> (rest : Stmt types stack out  return)
                   -> Stmt types stack out  return

      ||| A side effect, run.
      Print : (this : Expr types stack     STR)
           -> (rest : Stmt types stack out return)
                   -> Stmt types stack out return


      ||| Stop
      End : Stmt types stack stack this

      ||| Return a value.
      Return : (expr : Expr types stack       this)
                    -> Stmt types stack stack this

-- [ NOTE ]
--
-- TO assist in early return we distinguish between returning values
-- and the end of a computations:.

-- [ EOF ]
