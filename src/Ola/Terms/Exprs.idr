||| Expressions to work with values.
|||
||| Module    : Exprs.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
module Ola.Terms.Exprs

import Data.List.Elem
import public Data.Fin
import Data.Vect

import Ola.Terms.Types
import Ola.Terms.Vars

%default total


public export
data Expr : (types : List Ty)
         -> (stack : List Ty)

         -> (type  : Ty)
                  -> Type
  where
    Var : Var stack t -> Expr types stack t

    U : Expr types stack UNIT

    -- # Primitives

    -- ## Values
    C : Char   -> Expr types stack CHAR
    S : String -> Expr types stack STR
    I : Int    -> Expr types stack INT
    B : Bool   -> Expr types stack BOOL

    -- ## Operations

    Cond : (cond : Expr types stack BOOL)
        -> (tt   : Expr types stack a)
        -> (ff   : Expr types stack a)
                -> Expr types stack a

    -- Rest to come...
    -- @TODO primitive operations on char
    -- @TODO primitive operations on str
    -- @TODO primitive operations on Int
    -- @TODO primitive operations on bool

    -- # Data Structures

    -- ## Arrays

    -- ### Constructors
    ArrayEmpty : Expr types stack (ARRAY type Z)

    ArrayCons : Expr types stack        type
             -> Expr types stack (ARRAY type    n)
             -> Expr types stack (ARRAY type (S n))

    -- ### Eliminators
    Index : {n : Nat}
         -> (idx   : Fin n)
         -> (array : Expr types stack (ARRAY type n))
                  -> Expr types stack        type

    -- ## Products

    -- ### Constructors
    Pair : {a,b : Ty}
        -> Expr types stack       a
        -> Expr types stack         b
        -> Expr types stack (PAIR a b)

    -- ### Eliminators
    First : {a,b : Ty}
         -> Expr types stack (PAIR a b)
         -> Expr types stack       a

    Second : {a,b : Ty}
          -> Expr types stack (PAIR a b)
          -> Expr types stack         b

    -- ## Sums

    -- ### Constructors

    Left : Expr types stack        a
        -> Expr types stack (UNION a b)

    Right : Expr types stack          b
         -> Expr types stack (UNION a b)

    -- ### Eliminators

    Match : {a,b : Ty}
         -> (expr  : Expr types     stack  (UNION a b))
         -> (left  : Expr types (a::stack)  return)
         -> (right : Expr types (b::stack)  return)
                  -> Expr types     stack   return

    -- ## References

    Fetch : Expr types stack (REF t)
          -> Expr types stack      t

    Alloc : Expr types stack      type
         -> Expr types stack (REF type)

    Mutate : {type : Ty}
          -> Expr types stack (REF type)
          -> Expr types stack      type
          -> Expr types stack      UNIT

    -- ## Processes

    -- ### Open

    Open : (what : HandleKind)
        -> Expr types stack STR
        -> Expr types stack (UNION INT (HANDLE what))

    -- ### Read
    ReadLn : Expr types stack (HANDLE k)
          -> Expr types stack (UNION INT STR)

    -- ### Send
    WriteLn : Expr types stack (HANDLE k)
           -> Expr types stack STR
           -> Expr types stack (UNION INT UNIT)

    -- ### Close
    Close : Expr types stack (HANDLE k)
         -> Expr types stack (UNION INT UNIT)


    -- ## Function Application

    -- @TODO Make function application n-ary.
    Call : {a,b : Ty}
        -> Expr types stack (FUNC a b)
        -> Expr types stack       a
        -> Expr types stack         b

    -- ## Type Ascriptions
    The : (ty   : Ty   types       type)
       -> (expr : Expr types stack type)
               -> Expr types stack type

-- [ EOF ]
