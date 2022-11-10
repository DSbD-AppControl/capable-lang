||| Views on Types.
|||
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Ola.Raw.Types

import Data.Vect

import Toolkit.Data.DVect

import Toolkit.Data.Location

import Ola.Types
import Ola.Raw.AST

%default total


mutual

  public export
  data Args : (rs : Vect n (Raw.AST.TYPE))
                 -> Type
    where

      Nil : Args Nil

      (::) : (ty   : Ty   r)
          -> (rest : Args rs)
                   -> Args (r :: rs)

  public export
  data Ty : Raw.AST.TYPE -> Type
    where

      TyVar : (r : Ref)
           -> (prf : AsRef s fc r)
                -> Ty (Branch (VARTY s) fc Nil)

      TyChar : (fc : FileContext) -> Ty (Branch CHAR fc Nil)
      TyStr  : (fc : FileContext) -> Ty (Branch STR  fc Nil)
      TyInt  : (fc : FileContext) -> Ty (Branch INT  fc Nil)
      TyBool : (fc : FileContext) -> Ty (Branch BOOL fc Nil)
      TyUnit : (fc : FileContext) -> Ty (Branch UNIT fc Nil)

      TyArray : (fc : FileContext)
             -> (n  : Int)
             -> (ty : Ty t)
                   -> Ty (Branch (ARRAY n) fc [t])

      TyPair : (fc : FileContext)
            -> (l  : Ty lr)
            -> (r  : Ty rr)
                  -> Ty (Branch PROD fc [lr,rr])

      TyUnion : (fc : FileContext)
             -> (l  : Ty                lr)
             -> (r  : Ty                   rr)
                   -> Ty (Branch UNION fc [lr, rr])

      TyRef : (fc : FileContext)
           -> (ty : Ty           type)
                 -> Ty (Branch REF fc [type])

      TyHandle : (fc : FileContext)
              -> (k  : HandleKind)
                    -> Ty (Branch (HANDLE k) fc Nil)


      TyFunc : {0 types' : Vect (S n) Raw.AST.TYPE}
            -> (fc    : FileContext)
            -> (prf   : AsVect types types')
            -> (argty : Args          (init types'))
            -> (retty : Ty            (last types'))
                     -> Ty (Branch ARROW fc types)


mutual
  toTypeArgs : (rs : Vect n Raw.AST.TYPE)
                -> Args rs
  toTypeArgs []
    = []
  toTypeArgs (x :: xs)
    = (assert_total $ toType x) :: toTypeArgs (xs)

  export
  toType : (r : Raw.AST.TYPE)
           -> Ty r
  toType (Branch CHAR annot Nil) = TyChar annot
  toType (Branch STR annot Nil) = TyStr annot
  toType (Branch INT annot Nil) = TyInt annot
  toType (Branch BOOL annot Nil) = TyBool annot
  toType (Branch UNIT annot Nil) = TyUnit annot
  toType (Branch (HANDLE x) annot Nil) = TyHandle annot x
  toType (Branch (VARTY str) annot Nil) = TyVar (MkRef annot str) R
  toType (Branch REF annot [t]) = TyRef annot (toType t)
  toType (Branch (ARRAY i) annot [t]) = TyArray annot i (toType t)
  toType (Branch PROD annot [a,b]) = TyPair annot (toType a) (toType b)
  toType (Branch UNION annot [a,b]) = TyUnion annot (toType a) (toType b)

  toType (Branch ARROW fc nodes)
    = let (vs ** prf) = asVect nodes
      in TyFunc fc
                prf
                (toTypeArgs (init vs))
                (assert_total $ toType (last vs))

-- [ EOF ]
