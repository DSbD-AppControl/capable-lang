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
  data Stmt : (roles :         List Ty.Role)
           -> (types :         List Ty.Base)
           -> (stackI,stackO : List Ty.Base)
           -> (type  :                 Ty.Base)
                    -> Type
    where
      ||| Bind things to the stack!
      Let : {type : Ty.Base}
         -> (ty   : Ty         types                     type)
         -> (expr : Expr roles types          stack      type)
         -> (rest : Stmt roles types (type :: stack) out return)
                 -> Stmt roles types          stack  out return

      |||
      Mutate : {type  : Ty.Base}
            -> (loc   : Expr roles types stack      (REF type))
            -> (value : Expr roles types stack           type)
            -> (rest  : Stmt roles types stack out  return)
                     -> Stmt roles types stack out  return

      ||| Run a, possibly, side-effecting computation, and carry on.
      |||
      ||| We use this primarily to capture function calls.
      Run : {this : Ty.Base}
         -> (expr : Expr roles types stack     this)
         -> (rest : Stmt roles types stack out return)
                 -> Stmt roles types stack out return

      ||| A statement about binary decisions.
      Cond : (cond : Expr roles types stack      BOOL)
          -> (tt   : Stmt roles types stack outA return)
          -> (ff   : Stmt roles types stack outB return)
          -> (rest : Stmt roles types stack out  return)
                  -> Stmt roles types stack out  return

      ||| A statement about matching.
      Match : {a,b : Ty.Base}
           -> (expr  : Expr roles types     stack        (UNION a b))
           -> (left  : Stmt roles types (a::stack) outA return)
           -> (right : Stmt roles types (b::stack) outB return)
           -> (rest  : Stmt roles types     stack  out  return )
                    -> Stmt roles types     stack  out  return

      ||| A statement about splitting
      Split : {a,b : Ty.Base}
           -> (expr : Expr roles types        stack      (PAIR a b))
           -> (body : Stmt roles types (b::a::stack) out return)
                   -> Stmt roles types        stack  out return

      ||| A general while loop construct.
      |||
      While : (expr : Expr roles types stack      BOOL)
           -> (body : Stmt roles types stack outA return)
           -> (rest : Stmt roles types stack out  return)
                   -> Stmt roles types stack out  return

      ||| A side effect, run.
      Print : (this : Expr roles types stack     STR)
           -> (rest : Stmt roles types stack out return)
                   -> Stmt roles types stack out return


      ||| Stop
      End : Stmt roles types stack stack this

      ||| Return a value.
      Return : (expr : Expr roles types stack       this)
                    -> Stmt roles types stack stack this

-- [ NOTE ]
--
-- TO assist in early return we distinguish between returning values
-- and the end of a computations:.

-- [ EOF ]
