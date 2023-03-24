||| Various execution environments.
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
||| The design of the heap is based of of:
|||
||| Casper Bach Poulsen, Arjen Rouvoet, Andrew Tolmach, Robbert
||| Krebbers, and Eelco Visser. 2017. Intrinsically-typed definitional
||| interpreters for imperative languages. Proc. ACM Program. Lang. 2,
||| POPL, Article 16 (January 2018), 34
||| pages. https://doi.org/10.1145/3158104
|||
module Capable.Exec.Env

import Data.Vect

import Data.List.Elem
import Data.List.Quantifiers

import public Data.Singleton
import public Toolkit.Data.List.AtIndex
import Toolkit.Data.DList
import Toolkit.Data.Vect.Extra

import public Toolkit.DeBruijn.Renaming
import public Toolkit.DeBruijn.Environment

import Capable.Types

import Capable.Terms
import Capable.Terms

import Capable.Values

%default total
%hide type

||| Generic function to extend a stack by a given set of typed values
export
extend : DList Ty.Base (Value store)  types
      -> DList Ty.Base (Value store)           stack
      -> DList Ty.Base (Value store) (types ++ stack)
extend [] y = y
extend (elem :: rest) y = elem :: extend rest y

||| The stack.
|||
||| We divide into a local and global stack.
public export
data Env : (stack_g : List Ty.Method)
        -> (stack_l : List Ty.Base)
        -> (store   : List Ty.Base)
                   -> Type
  where
    MkEnv : (env_g : DList Ty.Method (Closure)     stack_g)
         -> (env_l : DList Ty.Base   (Value store) stack_l)
                  -> Env stack_g stack_l store

export
empty : Env Nil Nil Nil
empty = MkEnv Nil Nil


||| Extend the global stack with a value.
export
extend_g : {type : _}
        -> (val : Closure type)
        -> (env : Env        g  l store)
               -> Env (type::g) l store
extend_g val (MkEnv env_g env_l)
  = MkEnv (val :: env_g) env_l

||| Extend the local stack with a value.
export
extend_l : {type : _}
        -> (val : Value store type)
        -> (env : Env g        l  store)
               -> Env g (type::l) store
extend_l val (MkEnv env_g env_l)
  = MkEnv env_g (val :: env_l)

export
extend_ls : (val : DVect Ty.Base (Value store) n ts)
         -> (env : Env g                     l  store)
                -> Env g (Extra.toList ts ++ l) store
extend_ls Nil     env = env
extend_ls (x::xs) env = extend_l x (extend_ls xs env)

||| Lookup variable in the local context
export
lookup_l : (loc : IsVar l type)
        -> (env : Env g l store)
               -> Value store type
lookup_l loc (MkEnv env_g env_l)
  = read loc env_l

||| Lookup variable in the local context
export
lookup_g : (loc : IsVar g type)
        -> (env : Env g l store)
               -> Closure type
lookup_g loc (MkEnv env_g env_l)
  = read loc env_g

||| Weaken...
export
weaken : Subset old new
      -> Env.Env g l old
      -> Env.Env g l new
weaken prf (MkEnv env_g env_l)
  = MkEnv env_g
          (Env.weaken prf env_l)

namespace Ty
  ||| We need one for types-as-terms too.
  public export
  Env : (types : List Ty.Base)
              -> Type
  Env types = DList Ty.Base Singleton types

namespace Role
  ||| We need one for types-as-terms too.
  public export
  Env : (roles : List Ty.Role)
              -> Type
  Env roles = DList Ty.Role Singleton roles

namespace Heap
  ||| The heap.
  public export
  Heap : (store : List Ty.Base)
               -> Type
  Heap store = DList Ty.Base (Value store) store

  public export
  lookup : IsVar store type
        -> Heap  store
        -> Value store type
  lookup = read


  public export
  replace : IsVar store type
         -> Value store type
         -> Heap  store
         -> Heap  store
  replace = update


namespace Assigns

  public export
  data Assignments
       : (roles : List Ty.Role)
      -> (store : List Ty.Base)
      -> (prins : Roles roles ss)
               -> Type
    where
      Empty : Assignments roles store Nil
      KV : (loc : IsVar roles x)
        -> (val : Value store STR)
        -> (rest : Assignments roles store ps)
                -> Assignments roles store (loc :: ps)

||| Recursion variables are just closures...
|||
namespace RVars

  ||| We treat recursion in a session as a closure.
  public export
  data SubSesh : List Role -> List Role
              -> List Ty.Base
              -> List Ty.Session
              -> List Ty.Method
              ->      Ty.Base
              -> (rvar : Kind) -> Type where
    SS : {old : _}
      -> (expr : Expr rs
                      roles
                      types
                      globals
                      stack_g
                      stack_l
                      stack_r
                      whom body type)
      -> (envl : DList Ty.Base (Value old) stack_l)
      -> (envr : DList Kind (SubSesh rs roles types globals stack_g type) stack_r)
              -> SubSesh rs roles types globals stack_g type R


  ||| We need one for types-as-terms too.
  public export
  Env : List Role -> List Role
              -> List Ty.Base
                            -> List Ty.Session
              -> List Ty.Method
            -> (rs    : List Kind)
     -> (ty    :      Ty.Base)
              -> Type
  Env rs roles types globals stack_g rvars type
    = DList Kind (SubSesh rs roles types globals stack_g type) rvars

  export
  isSubset : {new, old : _}
          -> (heap : Heap new)
          -> (envl : DList Ty.Base (Value old) stack_l)
                  -> Dec (Subset old new)
  isSubset {new} {old} _ _ with (isSubset old new)
    isSubset {new = new} {old = old} _ _ | (Yes prf)
      = Yes prf
    isSubset {new = new} {old = old} _ _ | (No contra)
      = No $ (contra)

-- [ EOF ]
