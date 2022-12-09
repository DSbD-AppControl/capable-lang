||| Expressions to work with values.
|||
||| Module    : Exprs.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
module Capable.Terms.Exprs

import Data.List.Elem

import public Data.Fin

import Data.Vect

import System.File

import public Toolkit.Data.DList
import public Toolkit.Data.DVect

import Capable.Terms.Types
import Capable.Terms.Builtins
import Capable.Terms.Vars

%default total

%hide type

public export
index : (types : List (k,v)) -> List.Elem.Elem (s,t) types -> v
index ((s, t) :: xs) Here = t
index (y :: xs) (There x) = snd y


mutual
  public export
  data Case : (roles : List Ty.Role)
           -> (types : List Ty.Base)
           -> (stack : List Ty.Base)
           -> (ret  : Ty.Base)
           -> (spec : (String, Ty.Base))
                   -> Type
    where
      C : (s : String)
       -> Expr roles types (p::stack) return
       -> Case roles types     stack return (s,p)

  public export
  data Field : (roles : List Ty.Role)
            -> (types : List Ty.Base)
            -> (stack : List Ty.Base)
            -> (spec : (String, Ty.Base))
                   -> Type
    where
      F : (s : String)
       -> Expr roles types stack p
       -> Field roles types stack (s, p)

  public export
  data Expr : (roles : List Ty.Role)
           -> (types : List Ty.Base)
           -> (stack : List Ty.Base)

           -> (type  :      Ty.Base)
                    -> Type
    where
      Hole : String -> Expr roles types stack t
      Var : TyVar stack t -> Expr roles types stack t


      ||| Bind things to the stack!
      Let : {type : Ty.Base}
         -> (ty   : Ty         types                 type)
         -> (expr : Expr roles types          stack  type)
         -> (rest : Expr roles types (type :: stack) return)
                 -> Expr roles types          stack  return

      |||
      Seq : (this : Expr roles types stack UNIT)
         -> (that : Expr roles types stack typeB)
                 -> Expr roles types stack typeB

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


      -- # Data Structures

      -- ## Boolean Eliminator
      Cond : Expr roles types stack BOOL
          -> Expr roles types stack a
          -> Expr roles types stack a
          -> Expr roles types stack a


      -- ## Arrays

      -- ### Constructors
      ArrayEmpty : Expr roles types stack (ARRAY type Z)

      ArrayCons : Expr roles types stack        type
               -> Expr roles types stack (ARRAY type    n)
               -> Expr roles types stack (ARRAY type (S n))

      -- ### Eliminators
      Index : {n : Nat}
           -> (idx   : Expr roles types stack INT)
           -> (array : Expr roles types stack (ARRAY type n))
                    -> Expr roles types stack        type

      -- ## Products

      -- ### Constructors
      Tuple : (fields : DVect Base (Expr roles types stack) (S (S n)) as)
                     -> Expr roles types stack (TUPLE as)

      Set : {as : Vect (S (S n)) Base}
         -> (tuple : Expr roles types stack (TUPLE as))
         -> (idx   : Fin (S (S n)))
         -> (value : Expr roles types stack (index idx as))
                  -> Expr roles types stack (TUPLE as)

      -- ### Eliminators

      Get : {as    : Vect (S (S n)) Base}
         -> (tuple : Expr roles types stack (TUPLE as))
         -> (idx   : Fin (S (S n)))
                  -> Expr roles types stack (index idx as)

      -- ## Records

      Record : (fields : DList (String,Base) (Field roles types stack) (a::as))
                      -> Expr roles types stack (RECORD (a:::as))

      SetR : {s,t,a,as : _}
          -> (re    : Expr roles types stack (RECORD (a:::as)))
          -> (idx   : Elem (s,t) (a::as))
          -> (value : Expr roles types stack t)
                   -> Expr roles types stack (RECORD (a:::as))

      -- ### Eliminators

      GetR : {s,t,a,as : _}
         -> (rec : Expr roles types stack (RECORD (a:::as)))
         -> (idx : Elem (s,t) (a::as))
                -> Expr roles types stack t
      -- ## Sums

      -- ### Constructors
      Tag : {a : _}
         -> (s : String)
         -> (value : Expr roles types stack a)
         -> (prf   : Elem (s,a) (x::xs))
                  -> Expr roles types stack (UNION (x:::xs))

      -- ### Eliminators

      Match : {return : Base}
           -> {a  : (String, Base)}
           -> {as : List (String, Base)}
           -> (expr  : Expr roles types stack (UNION (a:::as)))
           -> (cases : DList (String,Base)
                             (Case roles types stack return)
                             (a::as))
                    -> Expr roles types stack  return

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

      -- ## Loops
      ||| A general do-until loop construct.
      |||
      Loop : (body : Expr roles types stack return)
          -> (expr : Expr roles types stack BOOL)
                  -> Expr roles types stack return


-- [ EOF ]
