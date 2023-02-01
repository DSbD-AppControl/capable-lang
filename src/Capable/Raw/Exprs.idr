||| Views on Types.
|||
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Capable.Raw.Exprs

import        System.File.Mode
import public Data.Singleton

import Toolkit.Data.Location
import Toolkit.AST

import public Data.Vect
import public Data.Vect.Quantifiers

import Capable.Types
import Capable.Raw.AST
import Capable.Raw.Types

%default total

%hide fields

mutual
  public export
  data Case : (s : Raw.AST.CASE) -> Type where
    C : {sc   : EXPR} -> (fc : FileContext)
     -> (t,s  : String)
     -> (c  : Expr sc)
           -> Case (Branch (CASE t s) fc [sc])

  public export
  data Field : (rs : Raw.AST.FIELDV)
                   -> Type
    where
      F : {r   : Raw.AST.EXPR}
       -> (fc  : FileContext)
       -> (s   : String)
       -> (e   : Expr   r)

              -> Field (Branch (KV s) fc [r])

  public export
  data Expr : (s : Raw.AST.EXPR) -> Type
    where

      -- ## Bindings
      Hole : (ref : Ref)
          -> (prf : AsRef s fc ref)
                 -> Expr (Branch (HOLE s) fc Nil)

      Var : (ref : Ref)
         -> (prf : AsRef s fc ref)
                -> Expr (Branch (VAR s) fc Nil)

      LetTy : (fc : FileContext)
           -> (s   : String)
           -> (st    : Stored)
           -> (ty    : Ty t)
           -> (val   : Expr v)
           -> (scope : Expr body)
                    -> Expr (Branch (LETTY st s) fc [t,v,body])

      Let   : (fc : FileContext)
           -> (s   : String)
           -> (st    : Stored)
           -> (val   : Expr v)
           -> (scope : Expr body)
                    -> Expr (Branch (LET st s) fc [v,body])

      Split : (fc    : FileContext)
           -> (ss    : List String)
           -> (val   : Expr v)
           -> (scope : Expr body)
                    -> Expr (Branch (SPLIT ss) fc [v,body])

      -- ## Builtin
      Const : (fc : FileContext)
           -> (p  : PrimVal)
           -> (v  : InterpPVal p)
                 -> Expr (Branch (CONST p v) fc [])

      OpBin : (fc : FileContext)
           -> (k  : BuiltinBinOps)
           -> (l  : Expr a)
           -> (r  : Expr b)
                 -> Expr (Branch (BBIN k) fc [a,b])

      OpUn : (fc : FileContext)
          -> (k  : BuiltinUnOps)
          -> (o  : Expr a)
                -> Expr (Branch (BUN k) fc [a])

      -- ## Data

      -- ### Arrays
      ArrayEmpty : (fc : FileContext)
                -> Expr (Branch NIL fc Nil)

      ArrayCons : (fc : FileContext)
               -> (head : Expr h)
               -> (tail : Expr t)
                       -> Expr (Branch CONS fc [h,t])

      Index : (fc  : FileContext)
           -> (idx : Expr i)
           -> (tm  : Expr t)
                  -> Expr (Branch IDX fc [i,t])

      Slice : (fc : FileContext)
           -> (st : Expr s)
           -> (ed : Expr e)
           -> (tm : Expr t)
                 -> Expr (Branch SLICE fc [s,e,t])

      -- ### Products
      MkTuple : {as' : Vect (S (S n)) Raw.AST.EXPR}
             -> (fc  : FileContext)
             -> (prf : AsVect as as')
             -> (ars : All Expr as')
                   -> Expr (Branch TUPLE fc as)

      Get : (fc : FileContext)
         -> (loc : Int)
         -> (tup : Expr e)
                -> Expr (Branch (GET loc) fc [e])

      Set : (fc : FileContext)
         -> (loc : Int)
         -> (tup : Expr e)
         -> (v   : Expr ev)
                -> Expr (Branch (SET loc) fc [e,ev])

      -- ### Structs

      Record : {fields' : Vect (S n) Raw.AST.FIELDV}
            -> (fc  : FileContext)
            -> (prf : AsVect fields fields')
            -> (fs  : All Field fields' )
                  -> Expr (Branch RECORD fc fields)

      GetR : (fc : FileContext)
         -> (loc : String)
         -> (tup : Expr e)
                -> Expr (Branch (GETR loc) fc [e])

      SetR : (fc : FileContext)
         -> (loc : String)
         -> (tup : Expr e)
         -> (v   : Expr ev)
                -> Expr (Branch (SETR loc) fc [e,ev])

      -- ### Unions

      Match : {cases'     : Vect (S n) Raw.AST.CASE}
           -> (fc     : FileContext)
           -> (cond   : Expr c)
           -> (prf    : AsVect cs cases')
           -> (cases  : All Case cases')
                     -> Expr (Branch (MATCH) fc (c::cs))

      Tag : (fc : FileContext)
         -> (s : String)
         -> (tm : Expr t)
                -> Expr (Branch (TAG s) fc [t])


      -- ### Ascriptions
      The : (fc : FileContext)
         -> (ty : Ty   t)
         -> (tm : Expr e)
               -> Expr (Branch THE fc [t,e])

      -- ### Control Flow
      Cond : (fc : FileContext)
          -> (c  : Expr cond)
          -> (t  : Expr tt)
          -> (f  : Expr ff)
                -> Expr (Branch COND fc [cond, tt, ff])

      Seq : (fc : FileContext)
         -> (this : Expr a)
         -> (that : Expr b)
                 -> Expr (Branch SEQ fc [a,b])

      Loop : (fc    : FileContext)
          -> (scope : Expr a)
          -> (cond  : Expr b)
                   -> Expr (Branch LOOP fc [a,b])

      Call : {as   : Vect n Raw.AST.EXPR}
          -> (fc   : FileContext)
          -> (fun  : Ref)
          -> (prf  : AsRef s fc ref)
          -> (prf  : AsVect args as)
          -> (argz : All Expr as)
                  -> Expr (Branch (CALL s) fc args)

mutual

  toCases : (ss : Vect n Raw.AST.CASE) -> All Case ss
  toCases [] = []
  toCases ((Branch (CASE str str1) annot [c]) :: xs)
    = C annot str str1 (toExpr c) :: toCases xs

  toFields : (ss : Vect n Raw.AST.FIELDV) -> All Field ss
  toFields [] = []
  toFields ((Branch (KV str) annot [c]) :: xs)
    = F annot str (toExpr c) :: toFields xs

  args : (az : Vect n EXPR)
                    -> All Expr az
  args [] = []
  args (ex :: rest)
    = toExpr ex :: args rest

  export
  toExpr : (e : Raw.AST.EXPR) -> Expr e
  toExpr (Branch (HOLE str) fc Nil)
    = Hole (MkRef fc str) R

  toExpr (Branch (VAR str) fc Nil)
    = Var (MkRef fc str) R

  toExpr (Branch (LETTY x str) fc [ty,v,s])
    = LetTy fc
            str
            x
            (toType ty)
            (toExpr v)
            (toExpr s)

  toExpr (Branch (LET x str) fc [v,s])
    = Let fc str x (toExpr v) (toExpr s)

  toExpr (Branch (SPLIT ss) fc [v,s])
    = Split fc ss (toExpr v) (toExpr s)

  toExpr (Branch (CONST p v) fc Nil)
    = Const fc p v

  toExpr (Branch (BBIN k) fc [l,r])
    = OpBin fc k (toExpr l) (toExpr r)

  toExpr (Branch (BUN k) fc [o])
    = OpUn fc k (toExpr o)

  toExpr (Branch NIL fc Nil)
    = ArrayEmpty fc

  toExpr (Branch CONS fc [h,t])
    = ArrayCons fc (toExpr h) (toExpr t)

  toExpr (Branch IDX fc [i,a])
    = Index fc (toExpr i) (toExpr a)

  toExpr (Branch SLICE fc [s,e,a])
    = Slice fc (toExpr s) (toExpr e) (toExpr a)

  toExpr (Branch TUPLE fc (f::s::fs))
    = let (as ** prf) = asVect (f::s::fs)
      in MkTuple fc prf (assert_total $ args as)

  toExpr (Branch (GET i) fc [f]) = Get fc i (toExpr f)
  toExpr (Branch (SET i) fc [f,e]) = Set fc i (toExpr f) (toExpr e)

  toExpr (Branch RECORD fc fs)
    = let (as ** prf) = asVect fs
      in Record fc prf (assert_total toFields as)

  toExpr (Branch (GETR i) fc [f]) = GetR fc i (toExpr f)
  toExpr (Branch (SETR i) fc [f,e]) = SetR fc i (toExpr f) (toExpr e)


  toExpr (Branch (TAG s) fc [l])
    = Tag fc s (toExpr l)


  toExpr (Branch MATCH fc (c::cs))
    = let (as ** prf) = asVect cs
      in Match fc (toExpr c) prf (assert_total $ toCases as)

  toExpr (Branch THE fc [ty,tm])
    = The fc (toType ty)
             (toExpr tm)

  toExpr (Branch COND fc [c,t,f])
    = Cond fc (toExpr c)
              (toExpr t)
              (toExpr f)

  toExpr (Branch SEQ fc [f,s])
    = Seq fc (toExpr f)
             (toExpr s)

  toExpr (Branch LOOP fc [s,c])
    = Loop fc (toExpr s)
              (toExpr c)

  toExpr (Branch (CALL s) fc as)
    = let (as ** prf) = asVect as
      in Call fc (MkRef fc s)
                 R
                 prf
                 (assert_total $ args as)

export
getFC : {e : EXPR} -> Expr e -> Singleton (getFC e)
getFC x = Val (getFC e)

export
flattern : All Case cs -> List String
flattern [] = []
flattern ((C fc t s c) :: y) = t :: flattern y
-- [ EOF ]
