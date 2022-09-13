||| Various execution environments.
|||
||| Module    : Env.idr
||| Copyright : (c) Jan de Muijnck-Hughes
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
module Ola.Env

import Data.Vect

import Data.List.Elem
import Data.List.Quantifiers

import public Data.Singleton
import public Toolkit.Data.List.AtIndex
import Toolkit.Data.DList
import public Toolkit.DeBruijn.Renaming
import public Toolkit.DeBruijn.Environment
import Ola.Types

import Ola.Terms
import Ola.Terms

import Ola.Values

%default total

||| The stack is a list of values.
public export
Env : (stack : List Ty.Base)
   -> (store : List Ty.Base)
            -> Type
Env stack store = DList Ty.Base (Value store) stack

export
extend : DList Ty.Base (Value store) types
      -> Env stack store
      -> Env (types ++ stack) store
extend [] y = y
extend (elem :: rest) y = elem :: extend rest y


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
