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
import public Toolkit.DeBruijn.Context
import public Toolkit.DeBruijn.Context.Item

import public Capable.Types.Protocol.Local.Synth
import public Capable.Types.Protocol.Assignment

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
  data Expr : (roles   : List Ty.Role)
           -> (types   : List Ty.Base)
           -> (globals : List Ty.Session)
           -> (stack_g : List Ty.Method)
           -> (stack_l : List Ty.Base)
           -> (type    :      Ty.Base)
                      -> Type
    where
      Hole : String
          -> Expr roles types globals stack_g stack_l t

-- [ NOTE ] Removed because functions are _not_ base types...
--
-- @TODO move functions and 'types-as-terms' representation to their own term-space?

--      VarG : TyVar stack_g t
--          -> Expr roles types globals stack_g stack_l t

      Var : TyVar stack_l t
         -> Expr roles types globals stack_g stack_l t

      ||| Bind things to the *local* stack!
      Let : {type : Ty.Base}
         -> (ty   : Ty         types                                   type)
         -> (expr : Expr roles types globals stack_g          stack_l  type)
         -> (rest : Expr roles types globals stack_g (type :: stack_l) return)
                 -> Expr roles types globals stack_g          stack_l  return

      ||| Split tuples by 'pattern matching'
      Split : {ss : _}
           -> (expr : Expr roles types globals stack_g                     stack_l  (TUPLE ss))
           -> (rest : Expr roles types globals stack_g (Extra.toList ss ++ stack_l) return)
                   -> Expr roles types globals stack_g                     stack_l  return

      |||
      Seq : (this : Expr roles types globals stack_g stack_l UNIT)
         -> (that : Expr roles types globals stack_g stack_l typeB)
                 -> Expr roles types globals stack_g stack_l typeB

      -- # Builtins

      ||| Builtin Operations
      |||
      ||| Covers:
      |||   1. Builtin constants
      |||   2. Operations on contant things.
      |||   3. Memory & Process APIs
      Builtin : {inputs : List Base}
             -> (desc   : Builtin                                         inputs return)
             -> (args   : DList Base (Expr roles types globals stack_g stack_l) inputs)
                       -> Expr             roles types globals stack_g stack_l         return


      -- # Data Structures

      -- ## Boolean Eliminator
      Cond : Expr roles types globals stack_g stack_l BOOL
          -> Expr roles types globals stack_g stack_l a
          -> Expr roles types globals stack_g stack_l a
          -> Expr roles types globals stack_g stack_l a


      -- ## Arrays

      -- ### Constructors
      VectorEmpty : Expr roles types globals stack_g stack_l (VECTOR type Z)

      VectorCons : Expr roles types globals stack_g stack_l        type
               -> Expr roles types globals stack_g stack_l (VECTOR type    n)
               -> Expr roles types globals stack_g stack_l (VECTOR type (S n))

      -- ### Eliminators
      Index : {n : Nat}
           -> (idx   : Expr roles types globals stack_g stack_l INT)
           -> (array : Expr roles types globals stack_g stack_l (VECTOR type n))
                    -> Expr roles types globals stack_g stack_l        type

      -- ## Products

      -- ### Constructors
      Tuple : (fields : DVect Base (Expr roles types globals stack_g stack_l) (S (S n)) as)
                     -> Expr roles types globals stack_g stack_l (TUPLE as)

      Set : {as    : Vect (S (S n)) Base}
         -> (tuple : Expr roles types globals stack_g stack_l (TUPLE as))
         -> (idx   : Fin (S (S n)))
         -> (value : Expr roles types globals stack_g stack_l (index idx as))
                  -> Expr roles types globals stack_g stack_l (TUPLE as)

      -- ### Eliminators

      Get : {as    : Vect (S (S n)) Base}
         -> (tuple : Expr roles types globals stack_g stack_l (TUPLE as))
         -> (idx   : Fin (S (S n)))
                  -> Expr roles types globals stack_g stack_l (index idx as)

      -- ## Records

      Record : (fields : DList (String,Base)
                               (Field roles types globals stack_g stack_l) (a::as))
                      -> Expr roles types globals stack_g stack_l (RECORD (a:::as))

      SetR : {s,t,a,as : _}
          -> (re    : Expr roles types globals stack_g stack_l (RECORD (a:::as)))
          -> (idx   : Elem (s,t) (a::as))
          -> (value : Expr roles types globals stack_g stack_l t)
                   -> Expr roles types globals stack_g stack_l (RECORD (a:::as))

      -- ### Eliminators

      GetR : {s,t,a,as : _}
         -> (rec : Expr roles types globals stack_g stack_l (RECORD (a:::as)))
         -> (idx : Elem (s,t) (a::as))
                -> Expr roles types globals stack_g stack_l t
      -- ## Sums

      -- ### Constructors
      Tag : {a : _}
         -> (s : String)
         -> (value : Expr roles types globals stack_g stack_l a)
         -> (prf   : Elem (s,a) (x::xs))
                  -> Expr roles types globals stack_g stack_l (UNION (x:::xs))

      -- ### Eliminators

      Match : {return : Base}
           -> {a      : (String, Base)}
           -> {as     : List (String, Base)}
           -> (expr   : Expr roles types globals stack_g stack_l (UNION (a:::as)))
           -> (cases  : DList (String,Base)
                              (Case roles types globals stack_g stack_l return)
                              (a::as))
                     -> Expr roles types globals stack_g stack_l  return

      -- ## Type Ascriptions
      The : (ty   : Ty         types                    type)
         -> (expr : Expr roles types globals stack_g stack_l type)
                 -> Expr roles types globals stack_g stack_l type

      -- ## Loops
      ||| A general do-until loop construct.
      |||
      Loop : (body : Expr roles types globals stack_g stack_l return)
          -> (expr : Expr roles types globals stack_g stack_l BOOL)
                  -> Expr roles types globals stack_g stack_l return


      -- ## Function Application

      Call : {as : List Ty.Base}
          -> {b  : Ty.Base}
          -> (f  : IsVar stack_g (FUNC as b))
          -> (a  : DList Ty.Base (Expr roles types ss stack_g stack_l) as)
                -> Expr roles types globals stack_g stack_l         b

      -- ## Session Innvocation

      Run : {as        : List Ty.Base}
         -> {b         : Ty.Base}
         -> {ctzt      : Context Role rs}
         -> (f         : IsVar stack_g (SESH ctzt whom prot as b))
         -> (args_comm : Assignments rs roles types globals stack_g stack_l prot princs)
         -> (prf       : Protocol.HasRoles rs prot princs)

         -> (args_comp : DList Ty.Base (Expr roles types globals stack_g stack_l) as)
                      -> Expr roles types globals stack_g stack_l                        b


  public export
  data Case : (roles   : List Ty.Role)
           -> (types   : List Ty.Base)
           -> (globals : List Ty.Session)
           -> (stack_g : List Ty.Method)
           -> (stack_l : List Ty.Base)
           -> (ret     : Ty.Base)
           -> (spec    : (String, Ty.Base))
                      -> Type
    where
      C : (s    : String)
       -> (body : Expr roles types globals stack_g (p::stack_l) return)
               -> Case roles types globals stack_g     stack_l  return (s,p)

  public export
  data Field : (roles   : List Ty.Role)
            -> (types   : List Ty.Base)
            -> (globals : List Ty.Session)
            -> (stack_g : List Ty.Method)
            -> (stack_l : List Ty.Base)
            -> (spec    : (String, Ty.Base))
                       -> Type
    where
      F : (s : String)
       -> (v : Expr  roles types globals stack_g stack_l p)
            -> Field roles types globals stack_g stack_l (s, p)


  ||| A custom association list to collect roles and string expressions.
  |||
  ||| If roles where not De Bruijn indexed we could have used _just_
  ||| an instances of `DList`.
  public export
  data Assignments
     : (roles,rs : List Ty.Role)
    -> (types    : List Ty.Base)
    -> (globals  : List Ty.Session)
    -> (stack_g  : List Ty.Method)
    -> (stack_l  : List Ty.Base)
    -> (proto    : Synth.Local ks roles)
    -> (ps       : Roles roles ss)
                -> Type

    where
      Empty : Assignments roles rs t g sg sl p Nil

      KV : (whom : IsVar roles x)
        -> (val  : Expr              rs t g sg sl STR)
        -> (kvs  : Assignments roles rs t g sg sl p rest)
                -> Assignments roles rs t g sg sl p (whom::rest)
-- [ EOF ]
