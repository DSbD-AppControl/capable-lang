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

import System.File

import public Toolkit.Data.DList

import Ola.Terms.Types
import Ola.Terms.Vars

%default total


public export
data Expr : (roles : List Ty.Role)
         -> (types : List Ty.Base)
         -> (stack : List Ty.Base)

         -> (type  :      Ty.Base)
                  -> Type
  where
    Var : TyVar stack t -> Expr roles types stack t

    U : Expr roles types stack UNIT

    -- # Primitives

    -- ## Values
    C : Char   -> Expr roles types stack CHAR
    S : String -> Expr roles types stack STR
    I : Nat    -> Expr roles types stack INT
    B : Bool   -> Expr roles types stack BOOL

    -- ## Operations

    Cond : (cond : Expr roles types stack BOOL)
        -> (tt   : Expr roles types stack a)
        -> (ff   : Expr roles types stack a)
                -> Expr roles types stack a

    -- Rest to come...
    -- @TODO primitive operations on char
    -- @TODO primitive operations on str
    -- @TODO primitive operations on Int
    -- @TODO primitive operations on bool

    -- # Data Structures

    -- ## Arrays

    -- ### Constructors
    ArrayEmpty : Expr roles types stack (ARRAY type Z)

    ArrayCons : Expr roles types stack        type
             -> Expr roles types stack (ARRAY type    n)
             -> Expr roles types stack (ARRAY type (S n))

    -- ### Eliminators
    Index : {n : Nat}
         -> (idx   : Fin n)
         -> (array : Expr roles types stack (ARRAY type n))
                  -> Expr roles types stack        type

    -- ## Products

    -- ### Constructors
    Pair : {a,b : Ty.Base}
        -> Expr roles types stack       a
        -> Expr roles types stack         b
        -> Expr roles types stack (PAIR a b)

    -- ### Eliminators Are statements


    -- ## Sums

    -- ### Constructors

    Left : Expr roles types stack        a
        -> Expr roles types stack (UNION a b)

    Right : Expr roles types stack          b
         -> Expr roles types stack (UNION a b)

    -- ### Eliminators Are statements
    -- ## References

    Fetch : Expr roles types stack (REF type)
         -> Expr roles types stack      type

    Alloc : Expr roles types stack      type
         -> Expr roles types stack (REF type)

    -- ## Processes

    -- ### Open

    Open : (what : HandleKind)
        -> (m : Mode)
        -> Expr roles types stack STR
        -> Expr roles types stack (UNION INT (HANDLE what))

    -- ### Read
    ReadLn : {k : HandleKind}
          -> Expr roles types stack (HANDLE k)
          -> Expr roles types stack (UNION INT STR)

    -- ### Send
    WriteLn : {k : HandleKind}
           -> Expr roles types stack (HANDLE k)
           -> Expr roles types stack STR
           -> Expr roles types stack (UNION INT UNIT)

    -- ### Close
    Close : {k : HandleKind}
         -> Expr roles types stack (HANDLE k)
         -> Expr roles types stack UNIT


    -- ## Function Application

    Call : {as : List Ty.Base}
        -> {b : Ty.Base}
        -> Expr roles types stack (FUNC as b)
        -> DList Ty.Base (Expr roles types stack) as
        -> Expr roles types stack         b

    -- ## Type Ascriptions
    The : (ty   : Ty   types       type)
       -> (expr : Expr roles types stack type)
               -> Expr roles types stack type

-- [ EOF ]
