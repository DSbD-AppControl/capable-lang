module Toolkit.AST

import public Data.Vect
import public Toolkit.Data.Location
import public Toolkit.Data.DVect

public export
data AST : (desc       : (k     : kind)
                      -> (arity : Nat)
                      -> (meta  : Vect arity kind)
                               -> Type)
        -> (k          : kind)
        -> (annotation : Type)
                      -> Type
  where

  Branch : {0 node  : (k : kind) -> (n : Nat) -> Vect n kind -> Type}
        -> (  desc  : node k n meta)
        -> (  annot : a)
        -> (  nodes : DVect kind (\k => AST node k a) n meta)
                   -> AST node k a

export
getAnnotation : AST d k a -> a
getAnnotation (Branch kind annot nodes)
  = annot

export
Functor (AST kinds k) where
  map f (Branch kind annot nodes)
    = Branch kind (f annot) (mapV f nodes)

    where mapV : (f : a -> b) -> DVect d (\k => AST node k a) n ks
                              -> DVect d (\k => AST node k b) n ks
          mapV f [] = []
          mapV f (x :: xs) = map f x :: mapV f xs



namespace Generic
  export
  show : {0 node  : (k : kind) -> (n : Nat) -> Vect n kind -> Type}
      -> (showDesc : forall k, arity, ms . (desc : node k arity ms)
                          -> String)
      -> (showAnn  : (annot : a) -> String)
      -> (ast      : AST node k a)
                  -> String


  show k a (Branch kind annot nodes)
    = "(Branch \{k kind} \{a annot} \{showDVect (show k a) nodes})"

namespace Foo
  export
  show : {0 node  : (k : kind) -> (n : Nat) -> Vect n kind -> Type}
      -> (forall k, arity, ms . Show (node k arity ms))
      => Show a
      => (ast      : AST node k a)
                  -> String


  show (Branch kind annot nodes)
    = "(Branch \{show kind} \{show annot} \{showDVect Foo.show nodes})"

namespace Default
  export
   {0 node  : (k : kind) -> (n : Nat) -> Vect n kind -> Type}
   -> (forall k,n,ms . Show (node k n ms))
      => Show a
      => Show (AST node k a) where

        show = assert_total $ Foo.show


public export
data AsRef : String -> FileContext -> Ref -> Type where
  R : AsRef s fc (MkRef fc s)

export
asRef : (s : String) -> (fc : FileContext) -> AsRef s fc (MkRef fc s)
asRef s fc = R

namespace Singleton
  public export
  data Singleton : (Nat -> Type) -> Unit -> (n : Nat) -> Vect n Unit -> Type where
    Val : s n -> Singleton s () n (replicate n ())

public export
SHAPE : (k : Type) -> Type
SHAPE k = (kind : k) -> (n : Nat) -> (desc : Vect n k) -> Type

public export
NULL : (type : SHAPE k) -> k -> Type
NULL ty kind = ty kind 0 Nil

public export
null : (shape : NULL type kind) -> (annot : a) -> AST type kind a
null shape annot
  = Branch shape annot []

public export
UN : (type : SHAPE k) -> k -> k-> Type
UN ty a b = ty a _ [b]

public export
un : {kindB : _}
  -> (shape : UN type kindA kindB)
  -> (annot : a)
  -> (inner : AST type kindB a)
           -> AST type kindA a
un shape annot inner
  = Branch shape annot [inner]

public export
BIN : (type : SHAPE k) -> k -> k -> k-> Type
BIN ty a b c = ty a _ [b,c]

public export
bin : {kindB, kindC : _}
   -> (shape : BIN type kindA kindB kindC)
   -> (annot : a)
   -> (inA   : AST type kindB a)
   -> (inB   : AST type kindC a)
            -> AST type kindA a
bin shape annot iA iB
  = Branch shape annot [iA,iB]

public export
TRI : (type : SHAPE k) -> k -> k -> k -> k -> Type
TRI ty a b c d = ty a _ [b,c,d]

public export
tri : {kindB, kindC, kindD : _}
   -> (shape : TRI type kindA kindB kindC kindD)
   -> (annot : a)
   -> (inA   : AST type kindB a)
   -> (inB   : AST type kindC a)
   -> (inC   : AST type kindD a)
            -> AST type kindA a
tri shape annot iA iB iC
  = Branch shape annot [iA,iB,iC]

namespace Views

  public export
  data ByArity : (ast : AST shape kind annot) -> Type
    where
      NULL : {0 shape : (k : kind)
                     -> (n : Nat)
                     -> Vect n kind
                     -> Type}
          -> {0   as : Vect Z kind}
          -> {    bs : DVect kind (\k => AST shape k annot) Z as}
          -> (s : shape k 0 as)
          -> (a : annot)
               -> ByArity (Branch s a bs)

      UN : {0 shape  : (k : kind) -> (n : Nat) -> Vect n kind -> Type}
        -> (s : shape k 1 [k'])
        -> (a : annot)
        -> (n : AST shape k' annot)
             -> ByArity (Branch s a [n])

      BIN : {0 shape  : (k : kind) -> (n : Nat) -> Vect n kind -> Type}
        -> (s  : shape k 2 [ka, kb])
        -> (a  : annot)
        -> (na : AST shape ka annot)
        -> (nb : AST shape kb annot)
             -> ByArity (Branch s a [na,nb])

      TRI : {0 shape  : (k : kind) -> (n : Nat) -> Vect n kind -> Type}
        -> (s  : shape k 3 [ka, kb, kc])
        -> (a  : annot)
        -> (na : AST shape ka annot)
        -> (nb : AST shape kb annot)
        -> (nc : AST shape kc annot)
             -> ByArity (Branch s a [na,nb,nc])
      GEN : {0 shape  : (k : kind) -> (n : Nat) -> Vect n kind -> Type}
        -> (s  : shape k n as)
        -> (a  : annot)
        -> (bs : DVect kind (\k => AST shape k annot) n as)
             -> ByArity (Branch s a bs)

  export
  byArity : (ast : AST shape kind annot)
                -> ByArity ast
  byArity (Branch desc x [])
    = NULL desc x
  byArity (Branch desc x [n])
    = UN desc x n
  byArity (Branch desc x [a,b])
    = BIN desc x a b
  byArity (Branch desc x [a,b,c])
    = TRI desc x a b c
  byArity (Branch desc x rest)
    = GEN desc x rest

-- [ EOF ]
