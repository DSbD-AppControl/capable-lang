||| Type-checker for expressions.
|||
||| Module    : Types.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
module Ola.Check.Exprs

import Toolkit.Data.Location

import Ola.Types
import Ola.Core

import Ola.Raw.Types
import Ola.Raw.Types.View
import Ola.Raw.Exprs
import Ola.Raw.Exprs.View

import Ola.Check.Common
import Ola.Check.Types

import Ola.Terms.Vars
import Ola.Terms.Types
import Ola.Terms.Exprs

%default total

mutual
  check : {e     : Expr}
       -> {rs    : List Ty.Role}
       -> {ds,gs : List Ty.Base}
       -> (rho   : Context Ty.Role rs)
       -> (delta : Context Ty.Base ds)
       -> (gamma : Context Ty.Base gs)
       -> (syn   : Expr e)
               -> Ola (DPair Ty.Base (Expr rs ds gs))

  check rho delta gamma (Var ref)
    = do prf <- embedAtInfo
                  (span ref)
                  (NotBound ref)
                  (Lookup.lookup (get ref) gamma)
         let (ty ** (loc ** prfN)) = deBruijn prf
         pure (ty ** Var (V loc prfN))

  check rho delta gamma (U fc)
    = pure (_ ** U)
  check rho delta gamma (C fc v)
    = pure (_ ** C v)
  check rho delta gamma (S fc v)
    = pure (_ ** S v)
  check rho delta gamma (I fc v)
    = pure (_ ** I v)
  check rho delta gamma (B fc v)
    = pure (_ ** B v)

  check rho delta gamma (Cond fc c t f)
    = do (BOOL ** c) <- check rho delta gamma c
           | (ty ** _) => mismatchAt (getFC c) BOOL ty

         (tyT ** tt) <- check rho delta gamma t

         (tyF ** ff) <- check rho delta gamma f

         Refl <- embedAt
                   fc
                   (Mismatch tyT tyF)
                   (decEq tyT tyF)

         pure (_ ** Cond c tt ff)

  check rho delta gamma (Index fc n arr)
    = do (ARRAY ty m ** tm) <- check rho delta gamma arr
           | (ty ** _) => throwAt fc (ArrayExpected ty)

         idx <- embedAt
                  fc
                  (BoundsError n m)
                  (natToFin n m)

         pure (_ ** Index idx tm)

  check rho delta gamma (Pair fc a b)
    = do (tyA ** tmA) <- check rho delta gamma a
         (tyB ** tmB) <- check rho delta gamma b

         pure (_ ** Pair tmA tmB)

  check rho delta gamma (Fetch fc p)
    = do (REF t ** tm) <- check rho delta gamma p
           | (ty ** tm) => throwAt fc (RefExpected ty)

         pure (_ ** Fetch tm)

  check rho delta gamma (Open fc k m w)
    = do (STR ** tm) <- check rho delta gamma w
           | (ty ** _) => mismatchAt fc STR ty

         pure (_ ** Open k m tm)

  check rho delta gamma (Read fc h)
    = do (HANDLE k ** h) <- check rho delta gamma h
           | (ty ** _) =>  throwAt fc (HandleExpected ty)

         pure (_ ** ReadLn h)

  check rho delta gamma (Write fc h s)
    = do (HANDLE k ** h) <- check rho delta gamma h
           | (ty ** _) =>  throwAt fc (HandleExpected ty)

         (STR ** s) <- check rho delta gamma s
           | (ty ** _) => mismatchAt fc STR ty

         pure (_ ** WriteLn h s)

  check rho delta gamma (Close fc h)
    = do (HANDLE k ** h) <- check rho delta gamma h
           | (ty ** _) => throwAt fc (HandleExpected ty)

         pure (_ ** Close h)

  check {rs} {ds} {gs} rho delta gamma (Call fc f as)
    = do (FUNC tys ty ** f) <- check rho delta gamma f
           | (ty ** _) => throwAt fc (FunctionExpected ty)

         as <- checkArgs tys as

         pure (_ ** Call f as)



    where
      checkArgs : {as   : List Expr}
               -> (tys  : List Ty.Base)
               -> (args : DList Expr Expr as)
                       -> Ola (DList Ty.Base
                                     (Expr rs ds gs)
                                     tys)
      checkArgs [] []
        = pure Nil
      checkArgs [] (elem :: rest)

        = throwAt fc (RedundantArgs (size (elem :: rest)))

      checkArgs (x :: xs) []
        = throwAt fc (ArgsExpected (x::xs))

      checkArgs (x :: xs) (tm' :: tms)
        = do (ty ** tm) <- check rho delta gamma tm'

             Refl <- embedAt
                       (getFC tm')
                       (Mismatch x ty)
                       (decEq x ty)

             rest <- checkArgs xs tms

             pure (tm :: rest)

  check rho delta gamma (ArrayCons fc x (Null fc'))
    = do (ty ** tm) <- check rho delta gamma x

         pure (_ ** ArrayCons tm ArrayEmpty)


  check rho delta gamma (ArrayCons fc h rest)
    = do (ty ** head) <- check rho delta gamma h

         (ARRAY ty' n ** tail) <- check rho delta gamma rest
           | (ty ** _) => throwAt fc (ArrayExpected ty)

         Refl <- embedAt
                   fc
                   (ArrayAppend ty (ARRAY ty' n))
                   (decEq       ty        ty')
         pure (_ ** ArrayCons head tail)

  -- [ NOTE ]
  --
  -- There is not enough information to type sums (or empty arrays) in
  -- their introduction forms.  We will type them at binder locations,
  -- ascriptions, and as arguments.
  check rho delta gamma (Left fc p)
    = unknown fc

  check rho delta gamma (Right fc p)
    = unknown fc

  check rho delta gamma (Null fc)
    = unknown fc

  -- [ NOTE ]
  --
  -- Here we check ascriptions and especially the unknowns.
  check rho delta gamma (The fc ty expr)
    = do T ty tm e <- ascript fc rho delta gamma ty expr
         pure (ty ** e)

  export
  ascript : {e     : Expr}
         -> {rs    : List Ty.Role}
         -> {ds,gs : List Ty.Base}
         -> (fc    : FileContext)
         -> (rho   : Context Ty.Role rs)
         -> (delta : Context Ty.Base ds)
         -> (gamma : Context Ty.Base gs)
         -> (ty    : View.Ty t)
         -> (syn   : Expr e)
                  -> Ola (The rs ds gs)

  ascript fc rho delta gamma ty expr

    = do res <- typeCheck delta ty

         case (res,expr) of
           ((ARRAY ty' Z ** tm), Null fc')
             => pure (T (ARRAY ty' Z) tm ArrayEmpty)

           ((ARRAY ty' (S k) ** tm), Null fc')
             => mismatchAt fc (ARRAY ty' (S k)) (ARRAY ty' Z)

           ((UNION tyL tyR ** tm), (Left fc' l))
             => do (tyL' ** l) <- check rho delta gamma l

                   Refl <- compare fc tyL tyL'

                   pure (T (UNION tyL tyR) tm (Left l))

           ((UNION tyL tyR ** tm), (Right fc' r))
             => do (tyR' ** l) <- check rho delta gamma r

                   Refl <- compare fc tyR tyR'

                   pure (T (UNION tyL tyR) tm (Right l))

           ((ty ** tm), expr)
             => do (ty' ** e) <- check
                                   rho
                                   delta
                                   gamma
                                   expr

                   Refl <- compare fc ty ty'

                   pure (T ty tm e)


export
ascriptReflect : {e     : Expr}
              -> {rs    : List Ty.Role}
              -> {ds,gs : List Ty.Base}
              -> (rho   : Context Ty.Role rs)
              -> (delta : Context Ty.Base ds)
              -> (gamma : Context Ty.Base gs)
              -> (syn   : Expr e)
                       -> Ola (The rs ds gs)
ascriptReflect rho delta gamma syn
  = do (ty ** expr) <- check rho delta gamma syn
       tm <- typeReflect delta ty
       pure (T ty tm expr)


export
exprCheck : {e     : Expr}
         -> {rs    : List Ty.Role}
         -> {ds,gs : List Ty.Base}
         -> (rho   : Context Ty.Role rs)
         -> (delta : Context Ty.Base ds)
         -> (gamma : Context Ty.Base gs)
         -> (syn   : Expr e)
                 -> Ola (DPair Ty.Base (Expr rs ds gs))

exprCheck
  = check

namespace Raw
  export
  exprCheck : {rs    : List Ty.Role}
           -> {ds,gs : List Ty.Base}
           -> (rho   : Context Ty.Role rs)
           -> (delta : Context Ty.Base ds)
           -> (gamma : Context Ty.Base gs)
           -> (syn   : Expr)
                   -> Ola (DPair Ty.Base (Expr rs ds gs))
  exprCheck r d g e
    = check r d g (view e)
-- [ EOF ]
