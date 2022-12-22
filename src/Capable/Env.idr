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
module Capable.Env

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
data Env : (stack_g : List Ty.Base)
        -> (stack_l : List Ty.Base)
        -> (store   : List Ty.Base)
                   -> Type
  where
    MkEnv : (env_g : DList Ty.Base (Value store) stack_g)
         -> (env_l : DList Ty.Base (Value store) stack_l)
                  -> Env stack_g stack_l store

export
empty : Env Nil Nil Nil
empty = MkEnv Nil Nil


||| Extend the global stack with a value.
export
extend_g : {type : _}
        -> (val : Value store type)
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
               -> Value store type
lookup_g loc (MkEnv env_g env_l)
  = read loc env_g

||| Weaken...
export
weaken : Subset old new
      -> Env.Env g l old
      -> Env.Env g l new
weaken prf (MkEnv env_g env_l)
  = MkEnv (Env.weaken prf env_g)
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

-- [ EOF ]
