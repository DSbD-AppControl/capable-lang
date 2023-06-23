||| Values.
|||
||| Copyright : COPYRIGHT
||| License   : see LICENSE
|||
||| Based on work by:
|||
||| Casper Bach Poulsen, Arjen Rouvoet, Andrew Tolmach, Robbert
||| Krebbers, and Eelco Visser. 2017. Intrinsically-typed definitional
||| interpreters for imperative languages. Proc. ACM Program. Lang. 2,
||| POPL, Article 16 (January 2018), 34
||| pages. https://doi.org/10.1145/3158104
module Capable.Values

import Decidable.Equality

import Data.List.Elem
import Data.List1.Elem
import Data.Vect

import public Data.Singleton

import public System.File

import Text.PrettyPrint.Prettyprinter

import Toolkit.Data.DList
import Toolkit.Data.DVect
import Toolkit.Data.List.AtIndex
import Toolkit.DeBruijn.Renaming

import Capable.Bootstrap
import Capable.Types

import Capable.Terms

%default total
%hide type

-- Helper functions for working on lists, required for working with the heap.

namespace List
  public export
  snoc : (xs : List type)
      -> (x  :      type)
            -> List type
  snoc xs x = xs ++ [x]

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

  export
  isSubset : DecEq type
          => (xs,ys : List type)
                   -> Dec (Subset xs ys)
  isSubset [] ys
    = Yes Empty

  isSubset (x :: xs) []
    = No absurd

  isSubset (x :: xs) (y :: ys) with (decEq x y)
    isSubset (x :: xs) (x :: ys) | (Yes Refl) with (isSubset xs ys)
      isSubset (x :: xs) (x :: ys) | (Yes Refl) | (Yes prf)
        = Yes (Extend x prf)
      isSubset (x :: xs) (x :: ys) | (Yes Refl) | (No contra)
        = No $ \case (Extend x rest) => contra rest

    isSubset (x :: xs) (y :: ys) | (No contra)
      = No $ \case (Extend x rest) => contra Refl


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

||| We treat closures (global stack elements) seperatly from the local
||| stack and heap.
public export
data Closure : Ty.Method
            -> Type
  where
    ClosFunc : (scope : Func roles types globals stack_g (FUNC args ret))
            -> (env_g : DList Ty.Method (Closure) stack_g)
            -> (rs    : DList    Role   (Singleton) roles)
                     -> Closure (FUNC args ret)

    ClosSesh : {whom  : _}
            -> (ctzt  : Context Role rs)
            -> {l     : Synth.Local Nil rs}
            -> (scope : Session roles types globals stack_g (SESH ctzt whom l args ret))
            -> (env_g : DList Ty.Method (Closure)   stack_g)
                     -> Closure (SESH ctzt whom l args ret)

public export
resolve : HandleKind -> Type
resolve FILE = File
resolve PIPE = File
resolve PROCESS = SubProcess

mutual
  public export
  data Field : List Base -> (String, Base) -> Type
    where
      F : (s : String) -> (v : Value store t) -> Field store (s,t)


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

--      Clos : (scope : Func roles types globals ctxt (FUNC a b))
--          -> (env_g : DList Ty.Base (Value store) ctxt)
--                   -> Value store (FUNC a b)

      H : (k : HandleKind) -> resolve k -> Value store (HANDLE k)

      MkList : List (Value store ty)
            -> Value store (LIST ty)

      MkVect : Vect n (Value store ty)
            -> Value store (VECTOR ty n)

      Tuple : {ts : _} -> DVect Ty.Base (Value store) (S (S n)) ts
           -> Value store (TUPLE ts)

      Record : {t,ts : _} -> DList (String, Ty.Base)
                     (Field store)
                     (t::ts)
            -> Value store (RECORD (t:::ts))

      Tag : {a : _}
         -> (s : String)
         -> (prf : Elem (s,a) (x::xs))
         -> Value store a
         -> Value store (UNION (x:::xs))

export
Pretty (Closure type) where
  pretty (ClosFunc scope env rs)
    = parens (pretty "Function Closure...")

  pretty (ClosSesh rs scope env)
    = parens (pretty "Session Closure...")

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

  pretty (H k x)
    = group
    $ parens
    $ hsep [pretty "Handle", pretty (show k)]

  pretty (MkList xs)
    = list
    $ assert_total
    $ map pretty xs

  pretty (MkVect xs)
    = vect
    $ Base.toList
    $ assert_total
    $ map pretty xs

  pretty (Tuple x)
    = tupled
    $ Base.toList
    $ assert_total
    $ mapToVect (pretty)
                x

  pretty (Record xs)
    = fields
    $ assert_total
    $ fieldsp xs
    where field : {s,t : _} -> Field store (s,t) -> Doc ann
          field (F s t)
            = group
            $ hsep
            [ pretty s
            , equals
            , pretty t
            ]

          fieldsp : {ts : _}
                 -> DList (String, Base)
                          (Field store)
                          ts
                -> List (Doc ann)

          fieldsp Nil = Nil
          fieldsp (F s t::xs) = field (F s t) :: fieldsp xs

  pretty (Tag s prf x)
    = group
    $ hcat [pretty s, parens (pretty x)]

export
Show (Value x type) where
  show = (show . annotate () . pretty)

public export
size : Value store (VECTOR type n)
    -> (Singleton n)
size (MkVect [])
  = Val 0
size (MkVect (x :: xs))
  = let Val y' = (size (MkVect xs)) in Val (S y')

||| Best way to do it.
public export
index : (idx : Fin n)
     -> (xs  : Value store (VECTOR type n))
            -> Value store        type
index idx (MkVect xs)
  = Vect.index idx xs

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
--  weaken prf (Clos s e) = Clos s (weaken prf e)
  weaken prf (H k h) = H k h
  weaken prf (MkList xs)
    = MkList
    $ map (weaken prf) xs

  weaken prf (MkVect xs)
    = MkVect
    $ map (weaken prf) xs

  weaken prf (Record xs)
    = Record (weaken prf xs)

  weaken prf (Tuple xs)
    = Tuple (weaken prf xs)
  weaken prf (Tag s p x)
    = Tag s p (weaken prf x)

  namespace Field
    public export
    weaken : Subset xs ys -> Field xs f
                         -> Field ys f
    weaken prf (F s t)
      = F s
      $ weaken prf t

  namespace DList
    public export
    weaken : Subset xs ys
          -> DList (String,Ty.Base) (Field xs) stack
          -> DList (String,Ty.Base) (Field ys) stack
    weaken prf [] = []
    weaken prf (ex :: rest)
      =  weaken prf ex
      :: weaken prf rest

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

public export
strengthen : (heap : DList Ty.Base (Value xs) stack)
          -> (val  : Value Nil ty)
          -> (prf  : Subset Nil xs)
                  -> Value xs  ty
strengthen heap val prf
  = weaken prf val

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

--export
--fhandles : SubProcess -> Value xs POPEN2
--fhandles (MkSubProcess pid input output)
--  = Record [ F "writeTo" (H PROCESS input)
--           , F "readFrom"  (H PROCESS output)]

-- [ EOF ]
