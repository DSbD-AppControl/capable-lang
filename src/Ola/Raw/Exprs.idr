||| Views on Types.
|||
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Ola.Raw.Exprs

import        System.File.Mode
import public Data.Singleton

import Toolkit.Data.Location
import Toolkit.AST

import public Data.Vect
import public Data.Vect.Quantifiers

import Ola.Types
import Ola.Raw.AST
import Ola.Raw.Types

%default total


public export
data Expr : (s : Raw.AST.EXPR) -> Type
  where

    -- ## Bindings
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
    MkPair : (fc  : FileContext)
          -> (fst : Expr f)
          -> (snd : Expr s)
                 -> Expr (Branch PAIR fc [f,s])

    Split : (fc : FileContext)
         -> (cond : Expr c)
         -> (f,s : String)
         -> (scope : Expr b)
                  -> Expr (Branch (SPLIT f s) fc [c, b])

    -- ### Unions

    Match : (fc     : FileContext)
         -> (cond   : Expr c)
         -> (l      : String)
         -> (scopeL : Expr gol)
         -> (r      : String)
         -> (scopeR : Expr gor)
                  -> Expr (Branch (MATCH l r) fc [c, gol, gor])

    Left : (fc : FileContext)
        -> (tm : Expr t)
              -> Expr (Branch LEFT fc [t])

    Right : (fc : FileContext)
         -> (tm : Expr t)
               -> Expr (Branch RIGHT fc [t])

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
        -> (fun  : Expr f)
        -> (prf  : AsVect args as)
        -> (argz : All Expr as)
                -> Expr (Branch CALL fc (f::args))

mutual
  args : (az : Vect n EXPR)
                    -> All Expr az
  args [] = []
  args (ex :: rest)
    = toExpr ex :: args rest

  export
  toExpr : (e : Raw.AST.EXPR) -> Expr e
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

  toExpr (Branch PAIR fc [f,s])
    = MkPair fc (toExpr f) (toExpr s)

  toExpr (Branch (SPLIT str str1) fc [c,s])
    = Split fc (toExpr c) str str1 (toExpr s)

  toExpr (Branch LEFT fc [l])
    = Left fc (toExpr l)

  toExpr (Branch RIGHT fc [r])
    = Right fc (toExpr r)

  toExpr (Branch (MATCH str str1) fc [c, l,r])
    = Match fc (toExpr c) str (toExpr l) str1 (toExpr r)

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

  toExpr (Branch CALL fc (f::as))
    = let (as ** prf) = asVect as
      in Call fc (toExpr f)
                 prf
                 (assert_total $ args as)

export
getFC : {e : EXPR} -> Expr e -> Singleton (getFC e)
getFC x = Val (getFC e)

-- [ EOF ]
