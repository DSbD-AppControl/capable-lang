||| Values.
|||
||| Module    : Values.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
||| Based on work by:
|||
||| Casper Bach Poulsen, Arjen Rouvoet, Andrew Tolmach, Robbert
||| Krebbers, and Eelco Visser. 2017. Intrinsically-typed definitional
||| interpreters for imperative languages. Proc. ACM Program. Lang. 2,
||| POPL, Article 16 (January 2018), 34
||| pages. https://doi.org/10.1145/3158104
module Ola.Values

import Decidable.Equality

import Data.List.Elem
import Toolkit.Data.DList
import Data.Vect

import public System.File

import Ola.Types

import Ola.Terms

%default total

-- Helper functions for working on lists, required for working with the heap.

namespace List
  public export
  snoc : (xs : List type)
      -> (x  :      type)
            -> List type
  snoc xs x = xs ++ [x]

  public export
  map : (f : {x : type} -> etype x -> etype' x)
     -> DList type etype  xs
     -> DList type etype' xs
  map f [] = []
  map f (elem :: rest) = f elem :: map f rest

namespace DList


  public export
  snoc : {x : type} -> DList type etype xs
          -> etype x
          -> DList type etype (Values.List.snoc xs x)
  snoc [] z = z :: []
  snoc (elem :: rest) z = elem :: snoc rest z

namespace Prefix
  public export
  data Subset : (this, that : List type) -> Type
    where
      Empty : Subset Nil that
      Extend : (x : type)
            -> (rest : Subset     this        that)
                    -> Subset (x::this) (x :: that)


  export
  Uninhabited (Subset (x::xs) Nil) where
    uninhabited Empty impossible
    uninhabited (Extend _ rest) impossible


  public export
  snoc_elem : (xs : List type) -> (x : type) -> Elem x (xs ++ [x])
  snoc_elem [] x = Here
  snoc_elem (y :: ys) x = There (snoc_elem ys x)

  public export
  expand : Elem type xs
        -> Subset xs ys
        -> Elem type ys
  expand Here (Extend _ rest)
    = Here
  expand (There x) (Extend _ rest)
    = There (expand x rest)

  public export
  snoc_add : (x : type)
          -> (xs : List type)
          -> Subset xs (xs ++ [x])
  snoc_add x [] = Empty
  snoc_add x (y :: xs)
    = Extend y (snoc_add x xs)

  public export
  noChange : (xs : List type) -> Subset xs xs
  noChange [] = Empty
  noChange (x :: xs) = Extend x (noChange xs)

  public export
  trans : Subset xs ys
       -> Subset ys zs
       -> Subset xs zs
  trans Empty Empty
    = Empty
  trans Empty (Extend x rest)
    = Empty
  trans (Extend x rest) (Extend x z)
    = Extend x (trans rest z)

||| Values are resolved expressions, closures, and addresses.
public export
data Value : (store : List Ty)
          -> (type  : Ty)
                   -> Type
  where
    Address : Var store type -> Value store (REF type)

    U : Value store UNIT

    C : Char -> Value store CHAR
    S : String -> Value store STR
    I : Int    -> Value store INT
    B : Bool   -> Value store BOOL

    Clos : (scope : Func types ctxt  (FUNC a b))
        -> (env   : DList Ty (Value store) ctxt)
                 -> Value store (FUNC a b)

    H : (k : HandleKind) -> File -> Value store (HANDLE k)

    ArrayEmpty : Value store (ARRAY type Z)

    ArrayCons : Value store        type
             -> Value store (ARRAY type    n)
             -> Value store (ARRAY type (S n))

    Pair : Value store a
        -> Value store b
        -> Value store (PAIR a b)

    Left : Value store a
        -> Value store (UNION a b)

    Right : Value store b
         -> Value store (UNION a b)

||| Best way to do it.
public export
index : (idx : Fin n)
     -> (xs  : Value store (ARRAY type n))
            -> Value store        type

index FZ ArrayEmpty impossible
index (FS x) ArrayEmpty impossible

index FZ (ArrayCons x y)
  = x
index (FS z) (ArrayCons x y)
  = index z y


-- Working with intrinsically typed heaps requires us to adjust the
-- addresses when the heap is modified. This requires we also update
-- the stack.  These functions do that.

mutual
  public export
  weaken : Subset xs ys
        -> Value xs type
        -> Value ys type
  weaken prf (Address x) = Address (expand x prf)
  weaken prf U = U
  weaken prf (C x) = C x
  weaken prf (S x) = S x
  weaken prf (I x) = I x
  weaken prf (B x) = B x
  weaken prf (Clos s e) = Clos s (weaken prf e)
  weaken prf (H k h) = H k h
  weaken prf (ArrayEmpty) = ArrayEmpty
  weaken prf (ArrayCons x xs)
    = ArrayCons (weaken prf x) (weaken prf xs)

  weaken prf (Pair x y) = Pair (weaken prf x) (weaken prf y)
  weaken prf (Left x) = Left (weaken prf x)
  weaken prf (Right x) = Right (weaken prf x)

  namespace Env
    public export
    weaken : Subset xs ys
          -> DList Ty (Value xs) stack
          -> DList Ty (Value ys) stack
    weaken prf [] = []
    weaken prf (elem :: rest)
      = weaken prf elem :: Env.weaken prf rest

||| Easier to write some type-level functions.
public export
Val : Ty -> List Ty -> Type
Val type types = Value types type


namespace Return

  ||| This helps with control flow.
  public export
  data Return : List Ty -> Ty -> Type where
    End : Return store UNIT
    Ret : Value store ty -> Return store ty


-- [ EOF ]
