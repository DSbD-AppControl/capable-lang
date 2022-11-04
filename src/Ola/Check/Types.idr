||| Type-checker for bidirectional typed Syntax for types.
|||
||| Module    : Types.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
module Ola.Check.Types

import Toolkit.Data.Location
import Toolkit.Data.DList

import Data.Singleton

import Ola.Types
import Ola.Core

import Ola.Raw.Types
import Ola.Raw.Types.View

import Ola.Check.Common

import Ola.Terms.Vars
import Ola.Terms.Types

%default total

mutual
  checkArgs : {types : List Ty.Base}
           -> (ctxt  : Context Ty.Base types)
           -> (args  : Args as)
                    -> Ola (DPair (List Ty.Base)
                                  (DList Ty.Base (Ty types)))
  checkArgs ctxt Empty

    = pure (_ ** Nil)

  checkArgs ctxt (Extend fc ty rest)

    = do (a ** ty) <- check ctxt ty
         (as ** tys) <- checkArgs ctxt rest

         pure (_ ** ty :: tys)

  check : {types : List Ty.Base}
       -> (ctxt : Context Ty.Base types)
       -> (syn  : Ty r)
               -> Ola (DPair Ty.Base (Ty types))

  check ctxt (TyVar x)
    = do prf <- embedAtInfo
                  (span x)
                  (NotBound x)
                  (Lookup.lookup (get x) ctxt)
         let (ty ** (loc ** prfN)) = deBruijn prf
         pure (ty ** TyVar (V loc prfN))

  check ctxt (TyChar fc)
    = pure (_ ** TyChar)
  check ctxt (TyStr fc)
    = pure (_ ** TyStr)
  check ctxt (TyInt fc)
    = pure (_ ** TyInt)
  check ctxt (TyBool fc)
    = pure (_ ** TyBool)
  check ctxt (TyUnit fc)
    = pure (_ ** TyUnit)

  check ctxt (TyArray fc n ty)
    = do (ty ** tm) <- check ctxt ty
         if n < 0
           then throwAt fc NatExpected
           else pure (_ ** TyArray tm (cast {to=Nat} n))

  check ctxt (TyPair fc a b)
    = do (tyA ** a) <- check ctxt a
         (tyB ** b) <- check ctxt b

         pure (_ ** TyPair a b)

  check ctxt (TyUnion fc a b)
    = do (tyA ** a) <- check ctxt a
         (tyB ** b) <- check ctxt b

         pure (_ ** TyUnion a b)

  check ctxt (TyRef fc ty)
    = do (ty ** tm) <- check ctxt ty
         pure (_ ** TyRef tm)

  check ctxt (TyHandle fc k)
    = pure (_ ** TyHandle k)

  check ctxt (TyFunc fc argty retty)
    = do (tyA ** args) <- checkArgs ctxt argty
         (tyR ** ret)  <- check     ctxt retty

         pure (_ ** TyFunc args ret)

-- ## Check

export
typeCheck : {types : List Ty.Base}
         -> (ctxt  : Context Ty.Base types)
         -> (syn   : Ty r)
                  -> Ola (DPair Ty.Base (Ty types))
typeCheck
  = check

namespace Raw
  export
  typeCheck : {types : List Ty.Base}
           -> (ctxt  : Context Ty.Base types)
           -> (r     : Raw.Ty)
                    -> Ola (DPair Ty.Base (Ty types))
  typeCheck ctxt r
    = check ctxt (view r)

mutual
  typeReflectArgs : {types : List Ty.Base}
                 -> (delta : Context Ty.Base types)
                 -> (ts    : List Ty.Base)
                          -> Ola (DList Ty.Base (Ty types) ts)
  typeReflectArgs delta []
    = pure Nil

  typeReflectArgs delta (x :: xs)
    = pure $ (::) !(typeReflect     delta x)
                  !(typeReflectArgs delta xs)

  export
  typeReflect : {types : List Ty.Base}
           -> (delta : Context Ty.Base types)
           -> (type  : Ty.Base)
                    -> Ola (Ty types type)

  typeReflect delta CHAR
    = pure TyChar
  typeReflect delta STR
    = pure TyStr
  typeReflect delta INT
    = pure TyInt
  typeReflect delta BOOL
    = pure TyBool
  typeReflect delta (ARRAY x k)
    = pure (TyArray !(typeReflect delta x) k)
  typeReflect delta (PAIR x y)
    = pure (TyPair !(typeReflect delta x)
                   !(typeReflect delta y))

  typeReflect delta (UNION x y)
    = pure (TyUnion !(typeReflect delta x)
                    !(typeReflect delta y))

  typeReflect delta UNIT
    = pure TyUnit

  typeReflect delta (REF x)
    = pure (TyRef !(typeReflect delta x))

  typeReflect delta (HANDLE x)
    = pure (TyHandle x)
  typeReflect delta (FUNC xs x)
    = pure (TyFunc !(typeReflectArgs delta xs)
                   !(typeReflect     delta x))

-- [ EOF ]
