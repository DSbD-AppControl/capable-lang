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
import Ola.Terms.Builtins
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

    -- # Builtins

    ||| Builtin Operations
    |||
    ||| Covers:
    |||   1. Builtin constants
    |||   2. Operations on contant things.
    |||   3. Memory & Process APIs
    Builtin : {inputs : List Base}
           -> (desc : Builtin                             inputs return)
           -> (args : DList Base (Expr roles types stack) inputs)
                   -> Expr             roles types stack         return


    Cond : Expr roles types stack BOOL
        -> Expr roles types stack a
        -> Expr roles types stack a
        -> Expr roles types stack a
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
