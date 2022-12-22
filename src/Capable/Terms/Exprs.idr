||| Expressions for expressing in function bodies.
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Capable.Terms.Exprs

import Data.List.Elem

import public Data.Fin

import Data.Vect


import System.File

import public Toolkit.Data.DList
import public Toolkit.Data.DVect
import public Toolkit.Data.Vect.Extra

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
  data Case : (roles   : List Ty.Role)
           -> (types   : List Ty.Base)
           -> (stack_g : List Ty.Base)
           -> (stack_l : List Ty.Base)
           -> (ret     : Ty.Base)
           -> (spec    : (String, Ty.Base))
                      -> Type
    where
      C : (s    : String)
       -> (body : Expr roles types g (p::stack) return)
               -> Case roles types g     stack  return (s,p)

  public export
  data Field : (roles   : List Ty.Role)
            -> (types   : List Ty.Base)
            -> (stack_g : List Ty.Base)
            -> (stack_l : List Ty.Base)
            -> (spec    : (String, Ty.Base))
                       -> Type
    where
      F : (s : String)
       -> (v : Expr  roles types stack_g stack_l p)
            -> Field roles types stack_g stack_l (s, p)

  public export
  data Expr : (roles   : List Ty.Role)
           -> (types   : List Ty.Base)
           -> (stack_g : List Ty.Base)
           -> (stack_l : List Ty.Base)
           -> (type    :      Ty.Base)
                      -> Type
    where
      Hole : String -> Expr roles types stack_g stack_g t

      VarG : TyVar stack_g t -> Expr roles types stack_g stack_l t
      VarL : TyVar stack_l t -> Expr roles types stack_g stack_l t


      ||| Bind things to the *local* stack!
      Let : {type : Ty.Base}
         -> (ty   : Ty         types                           type)
         -> (expr : Expr roles types stack_g          stack_l  type)
         -> (rest : Expr roles types stack_g (type :: stack_l) return)
                 -> Expr roles types stack_g          stack_l  return

      ||| Split tuples by 'pattern matching'
      Split : {ss : _}
           -> (expr : Expr roles types stack_g                     stack_l  (TUPLE ss))
           -> (rest : Expr roles types stack_g (Extra.toList ss ++ stack_l) return)
                   -> Expr roles types stack_g                     stack_l  return

      |||
      Seq : (this : Expr roles types stack_g stack_l UNIT)
         -> (that : Expr roles types stack_g stack_l typeB)
                 -> Expr roles types stack_g stack_l typeB

      -- # Builtins

      ||| Builtin Operations
      |||
      ||| Covers:
      |||   1. Builtin constants
      |||   2. Operations on contant things.
      |||   3. Memory & Process APIs
      Builtin : {inputs : List Base}
             -> (desc   : Builtin                                       inputs return)
             -> (args   : DList Base (Expr roles types stack_g stack_l) inputs)
                       -> Expr             roles types stack_g stack_l         return


      -- # Data Structures

      -- ## Boolean Eliminator
      Cond : Expr roles types stack_g stack_l BOOL
          -> Expr roles types stack_g stack_l a
          -> Expr roles types stack_g stack_l a
          -> Expr roles types stack_g stack_l a


      -- ## Arrays

      -- ### Constructors
      ArrayEmpty : Expr roles types stack_g stack_l (ARRAY type Z)

      ArrayCons : Expr roles types stack_g stack_l        type
               -> Expr roles types stack_g stack_l (ARRAY type    n)
               -> Expr roles types stack_g stack_l (ARRAY type (S n))

      -- ### Eliminators
      Index : {n : Nat}
           -> (idx   : Expr roles types stack_g stack_l INT)
           -> (array : Expr roles types stack_g stack_l (ARRAY type n))
                    -> Expr roles types stack_g stack_l        type

      -- ## Products

      -- ### Constructors
      Tuple : (fields : DVect Base (Expr roles types stack_g stack_l) (S (S n)) as)
                     -> Expr roles types stack_g stack_l (TUPLE as)

      Set : {as    : Vect (S (S n)) Base}
         -> (tuple : Expr roles types stack_g stack_l (TUPLE as))
         -> (idx   : Fin (S (S n)))
         -> (value : Expr roles types stack_g stack_l (index idx as))
                  -> Expr roles types stack_g stack_l (TUPLE as)

      -- ### Eliminators

      Get : {as    : Vect (S (S n)) Base}
         -> (tuple : Expr roles types stack_g stack_l (TUPLE as))
         -> (idx   : Fin (S (S n)))
                  -> Expr roles types stack_g stack_l (index idx as)

      -- ## Records

      Record : (fields : DList (String,Base) (Field roles types stack_g stack_l) (a::as))
                      -> Expr roles types stack_g stack_l (RECORD (a:::as))

      SetR : {s,t,a,as : _}
          -> (re    : Expr roles types stack_g stack_l (RECORD (a:::as)))
          -> (idx   : Elem (s,t) (a::as))
          -> (value : Expr roles types stack_g stack_l t)
                   -> Expr roles types stack_g stack_l (RECORD (a:::as))

      -- ### Eliminators

      GetR : {s,t,a,as : _}
         -> (rec : Expr roles types stack_g stack_l (RECORD (a:::as)))
         -> (idx : Elem (s,t) (a::as))
                -> Expr roles types stack_g stack_l t
      -- ## Sums

      -- ### Constructors
      Tag : {a : _}
         -> (s : String)
         -> (value : Expr roles types stack_g stack_l a)
         -> (prf   : Elem (s,a) (x::xs))
                  -> Expr roles types stack_g stack_l (UNION (x:::xs))

      -- ### Eliminators

      Match : {return : Base}
           -> {a      : (String, Base)}
           -> {as     : List (String, Base)}
           -> (expr   : Expr roles types stack_g stack_l (UNION (a:::as)))
           -> (cases  : DList (String,Base)
                              (Case roles types stack_g stack_l return)
                              (a::as))
                     -> Expr roles types stack_g stack_l  return

      -- ## Function Application

      Call : {as : List Ty.Base}
          -> {b  : Ty.Base}
          -> (f  : Expr roles types stack_g stack_l (FUNC as b))
          -> (a  : DList Ty.Base (Expr roles types stack_g stack_l) as)
                -> Expr roles types stack_g stack_l         b

      -- ## Type Ascriptions
      The : (ty   : Ty         types                 type)
         -> (expr : Expr roles types stack_g stack_l type)
                 -> Expr roles types stack_g stack_l type

      -- ## Loops
      ||| A general do-until loop construct.
      |||
      Loop : (body : Expr roles types stack_g stack_l return)
          -> (expr : Expr roles types stack_g stack_l BOOL)
                  -> Expr roles types stack_g stack_l return

      -- ## Typed Sessions
      {-
      ||| Create a new session from the given global protocol projected as the given role.
      NewSession : (g_term     : Global Nil types roles g)
                -> (principle  : Role roles MkRole)
                -> (projection : Project Nil roles principle g l)
                -> (scope      : Expr roles types stack_g (stack_l) a)
                -- @TODO sort out what local types are...
                              -> Expr roles types stack_g stack_l a

      Crash : Expr roles types stack_g stack_l (L Crash)
           -> Expr roles types stack_g stack_l a

      End : Expr roles types stack_g stack_l (L End)
         -> Expr roles types stack_g stack_l a

      Rec : Expr roles types stack_g (L (Rec k) :: stack_l) (L k)
         -> Expr roles types stack_g               stack_l) (L (Rec k))

      Call : Expr roles types stack_g stack_l (Call X)
          -> Expr roles types stack_g stack_l a

      Send : Expr roles types stack_g stack_l ...
          -> (scope : Expr roles types stack_g stack_l )
          -> Expr roles types stack_g stack_l (L (Select ...))

      Offer : Expr roles types stack_g stack_l ...
          -> (cases : ...)
                   -> Expr roles types stack_g stack_l (L (Offer ...))
      {-
      Choice (Select and Offer)

      -}
      -}
-- [ EOF ]
