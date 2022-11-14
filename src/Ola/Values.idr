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
import Data.List1.Elem
import Data.Vect
import public Data.Singleton

import public System.File

import Text.PrettyPrint.Prettyprinter

import Toolkit.Data.DList
import Toolkit.Data.List.AtIndex
import Toolkit.DeBruijn.Renaming

import Ola.Bootstrap
import Ola.Types

import Ola.Terms

%default total
%hide type

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
  snoc_elem : {type : Type}
           -> (xs : List type)
           -> (x  : type)
           -> IsVar (xs ++ [x]) x
  snoc_elem [] x
    = V 0 Here
  snoc_elem (y :: ys) x with (snoc_elem ys x)
    snoc_elem (y :: ys) x | (V pos prf)
      = V (S pos) (There prf)

  public export
  expand : IsVar  xs type
         -> Subset      xs ys
         -> IsVar  ys type
  expand (V 0 Here) (Extend type rest)
    = V 0 Here
  expand (V (S k) (There later)) (Extend y rest) with (expand (V k later) rest)
    expand (V (S k) (There later)) (Extend y rest) | (V pos prf)
      = V (S pos) (There prf)


  public export
  snoc_add : (x  : type)
          -> (xs : List type)
                -> Subset xs (xs ++ [x])
  snoc_add x []
    = Empty
  snoc_add x (y :: xs)
    = Extend y (snoc_add x xs)

  public export
  noChange : (xs : List type)
                -> Subset xs xs
  noChange []
    = Empty
  noChange (x :: xs)
    = Extend x (noChange xs)

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
data Value : (store : List Ty.Base)
          -> (type  : Ty.Base)
                   -> Type
  where
    Address : IsVar store type -> Value store (REF type)

    U :           Value store UNIT

    C : Char   -> Value store CHAR
    S : String -> Value store STR
    I : Int    -> Value store INT
    B : Bool   -> Value store BOOL

    Clos : (scope : Func roles types ctxt  (FUNC a b))
        -> (env   : DList Ty.Base (Value store) ctxt)
                 -> Value store (FUNC a b)

    H : (k : HandleKind) -> File -> Value store (HANDLE k)

    ArrayEmpty : Value store (ARRAY type Z)

    ArrayCons : Value store        type
             -> Value store (ARRAY type    n)
             -> Value store (ARRAY type (S n))

    Tuple : {ts : _} -> DVect Ty.Base (Value store) (S (S n)) ts
         -> Value store (TUPLE ts)

    Tag : {a : _}
       -> (s : String)
       -> (prf : Elem (s,a) (x::xs))
       -> Value store a
       -> Value store (UNION (x:::xs))

export
Pretty (Value store type) where
  pretty (Address x)
    = group
    $ parens
    $ hsep [pretty "Addr", pretty x]

  pretty U = pretty "U"

  pretty (C c)
    = pretty c
  pretty (S str)
    = pretty str

  pretty (I i) = pretty i
  pretty (B x) = pretty x
  pretty (Clos scope env) = parens $ pretty "Closure..."
  pretty (H k x)
    = group
    $ parens
    $ hsep [pretty "Handle", pretty (show k)]

  pretty ArrayEmpty
    = pretty "{}"

  pretty (ArrayCons x y)
    = group
    $ parens
    $ hsep [pretty x, pretty "::", pretty y]

  pretty (Tuple x)
    = tupled
    $ Base.toList
    $ assert_total
    $ mapToVect (pretty)
                x

  pretty (Tag s prf x)
    = group
    $ hcat [pretty s, parens (pretty x)]

export
Show (Value x type) where
  show = (show . annotate () . pretty)

public export
size : Value store (ARRAY type n)
    -> (Singleton n)
size ArrayEmpty = (Val Z)
size (ArrayCons x y) = let Val y' = (size y) in Val (S y')

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

  weaken prf (Tuple xs)
    = Tuple (weaken prf xs)
  weaken prf (Tag s p x)
    = Tag s p (weaken prf x)

  namespace DVect
    public export
    weaken : Subset xs ys
          -> DVect Ty.Base (Value xs) n stack
          -> DVect Ty.Base (Value ys) n stack
    weaken prf [] = []
    weaken prf (ex :: rest)
      =  weaken prf ex
      :: weaken prf rest

  namespace Env
    public export
    weaken : Subset xs ys
          -> DList Ty.Base (Value xs) stack
          -> DList Ty.Base (Value ys) stack
    weaken prf [] = []
    weaken prf (elem :: rest)
      = weaken prf elem :: Env.weaken prf rest

||| Easier to write some type-level functions.
public export
Val : Ty.Base -> List Ty.Base -> Type
Val type types = Value types type


public export
FileEither : Base -> Base
FileEither rt
  = UNION
  $ ("left", INT) ::: [("right", rt)]

export
left : (rty : Base)
    -> (Value xs INT) -> Value xs (FileEither rty)
left _ = Tag "left" Here

export
right : (rty : Base)
    -> (Value xs rty) -> Value xs (FileEither rty)
right _ = Tag "right" (There Here)

-- [ EOF ]
