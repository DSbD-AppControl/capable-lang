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
import public Ola.Terms.Builtins
import Ola.Terms.Types
import Ola.Terms.Exprs

%default total

mutual
  checkBinOpB : {a,b     : Expr}
          -> {rs    : List Ty.Role}
          -> {ds,gs : List Ty.Base}
          -> (rho   : Context Ty.Role rs)
          -> (delta : Context Ty.Base ds)
          -> (gamma : Context Ty.Base gs)
          -> (fc    : FileContext)
          -> (synA   : Expr a)
          -> (synb  : Expr b)
                   -> BinOpBoolKind
               -> Ola (Expr rs ds gs BOOL)
  checkBinOpB rho delta gamma fc l r k
    = do T tyTm l <- ascript fc rho delta gamma TyBool l
         T tyTm r <- ascript fc rho delta gamma TyBool r

         pure (Builtin (BinOpBool k) [l, r])

  checkBinOpI : {a,b     : Expr}
          -> {rs    : List Ty.Role}
          -> {ds,gs : List Ty.Base}
          -> (rho   : Context Ty.Role rs)
          -> (delta : Context Ty.Base ds)
          -> (gamma : Context Ty.Base gs)
          -> (fc    : FileContext)
          -> (synA   : Expr a)
          -> (synb  : Expr b)
                   -> BinOpIntKind
               -> Ola (Expr rs ds gs INT)
  checkBinOpI rho delta gamma fc l r k
    = do T tyTm l <- ascript fc rho delta gamma TyInt l
         T tyTm r <- ascript fc rho delta gamma TyInt r

         pure (Builtin (BinOpInt k) [l, r])


  checkCmp : {a,b     : Expr}
          -> {rs    : List Ty.Role}
          -> {ds,gs : List Ty.Base}
          -> (rho   : Context Ty.Role rs)
          -> (delta : Context Ty.Base ds)
          -> (gamma : Context Ty.Base gs)
          -> (fc    : FileContext)
          -> (synA   : Expr a)
          -> (synb  : Expr b)
          -> BinOpCmpKind
               -> Ola (Expr rs ds gs BOOL)
  checkCmp rho delta gamma fc l r k
    = do (tyL ** l) <- check rho delta gamma l
         (tyR ** r) <- check rho delta gamma r

         Refl <- compare fc tyL tyR

         maybe (throwAt fc Uncomparable)
               (\prf => pure (Builtin (Cmp prf k) [l, r]))
               (cmpTy tyL)

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
    = pure (_ ** Builtin U Nil)
  check rho delta gamma (C fc v)
    = pure (_ ** Builtin (C v) Nil)
  check rho delta gamma (S fc v)
    = pure (_ ** Builtin (S v) [])
  check rho delta gamma (I fc v)
    = pure (_ ** Builtin (I v) [])
  check rho delta gamma (B fc v)
    = pure (_ ** Builtin (B v) [])

  check rho delta gamma (And fc l r)
    = pure (_ ** !(checkBinOpB rho delta gamma fc l r AND))

  check rho delta gamma (Or fc l r)
    = pure (_ ** !(checkBinOpB rho delta gamma fc l r OR))

  check rho delta gamma (Not fc l)
    = do T tyTm l <- ascript fc rho delta gamma (TyBool) l
         pure ( _ ** Builtin Not [l])

  check rho delta gamma (LT fc l r)
    = pure (_ ** !(checkCmp rho delta gamma fc l r LT))

  check rho delta gamma (LTE fc l r)
    = pure (_ ** !(checkCmp rho delta gamma fc l r LTE))

  check rho delta gamma (GT fc l r)
    = pure (_ ** !(checkCmp rho delta gamma fc l r GT))

  check rho delta gamma (GTE fc l r)
    = pure (_ ** !(checkCmp rho delta gamma fc l r GTE))

  check rho delta gamma (EQ fc l r)
    = pure (_ ** !(checkCmp rho delta gamma fc l r EQ))

  check rho delta gamma (Sub fc l r)
    = pure (_ ** !(checkBinOpI rho delta gamma fc l r SUB))

  check rho delta gamma (Div fc l r)
    = pure (_ ** !(checkBinOpI rho delta gamma fc l r DIV))

  check rho delta gamma (Mul fc l r)
    = pure (_ ** !(checkBinOpI rho delta gamma fc l r MUL))

  check rho delta gamma (Add fc l r)
    = pure (_ ** !(checkBinOpI rho delta gamma fc l r ADD))

  check rho delta gamma (Ord fc l)
    = do T tyTm l <- ascript fc rho delta gamma (TyChar) l
         pure (_ ** Builtin (CharOp Ord) [l])

  check rho delta gamma (Chr fc l)
    = do T tyTm l <- ascript fc rho delta gamma (TyInt) l
         pure (_ ** Builtin (CharOp Chr) [l])

  check rho delta gamma (Str fc l)
    = do T tyTm l <- ascript fc rho delta gamma (TyChar) l
         pure (_ ** Builtin (CharOp Singleton) [l])

  check rho delta gamma (ToString fc l)
    = do (ty ** l) <- check rho delta gamma l

         maybe (throwAt fc Uncomparable)
               (\prf => pure (_ ** Builtin (ToString prf) [l]))
               (cmpTy ty)

  check rho delta gamma (Slice fc l k j)
    = do T tyTm l <- ascript fc rho delta gamma (TyInt) l
         T tyTm k <- ascript fc rho delta gamma (TyInt) k
         T tyTm j <- ascript fc rho delta gamma (TyStr) j
         pure (_ ** Builtin (StrOp Slice) [l, k, j])

  check rho delta gamma (Size fc l)
    = do T tyTm l <- ascript fc rho delta gamma (TyStr)  l
         pure (_ ** Builtin (StrOp Length) [l])

  check rho delta gamma (Cons fc l r)
    = do T tyTm l <- ascript fc rho delta gamma (TyChar) l
         T tyTm r <- ascript fc rho delta gamma (TyStr)  r
         pure (_ ** Builtin (StrOp Cons) [l, r])


  check rho delta gamma (Cond fc c t f)
    = do T _ c <- ascript (getFC c) rho delta gamma TyBool c

         (tyT ** tt) <- check rho delta gamma t

         (tyF ** ff) <- check rho delta gamma f

         Refl <- compare fc tyT tyF

         pure (_ ** Cond c tt ff)

  check rho delta gamma (Index fc n arr)
    = do (ARRAY ty m ** tm) <- check rho delta gamma arr
           | (ty ** _) => throwAt fc (ArrayExpected ty)

         if n < 0
           then throwAt fc NatExpected
           else do idx <- embedAt
                            fc
                            (BoundsError (cast n) m)
                            (natToFin (cast n) m)

                   pure (_ ** Index idx tm)

  check rho delta gamma (Pair fc a b)
    = do (tyA ** tmA) <- check rho delta gamma a
         (tyB ** tmB) <- check rho delta gamma b

         pure (_ ** Pair tmA tmB)

  check rho delta gamma (Fetch fc p)
    = do (REF t ** tm) <- check rho delta gamma p
           | (ty ** tm) => throwAt fc (RefExpected ty)

         pure (_ ** Builtin Fetch [tm])

  check rho delta gamma (Open fc k m w)
    = do (STR ** tm) <- check rho delta gamma w
           | (ty ** _) => mismatchAt fc STR ty

         pure (_ ** Builtin (Open k m) [tm])

  check rho delta gamma (Read fc h)
    = do (HANDLE k ** h) <- check rho delta gamma h
           | (ty ** _) =>  throwAt fc (HandleExpected ty)

         pure (_ ** Builtin ReadLn [h])

  check rho delta gamma (Write fc h s)
    = do (HANDLE k ** h) <- check rho delta gamma h
           | (ty ** _) =>  throwAt fc (HandleExpected ty)

         (STR ** s) <- check rho delta gamma s
           | (ty ** _) => mismatchAt fc STR ty

         pure (_ ** Builtin WriteLn [h, s])

  check rho delta gamma (Close fc h)
    = do (HANDLE k ** h) <- check rho delta gamma h
           | (ty ** _) => throwAt fc (HandleExpected ty)

         pure (_ ** Builtin Close [h])

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
    = do (_ ** T tm e) <- ascript fc rho delta gamma ty expr
         pure (_ ** e)


  namespace View
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
                    -> Ola (DPair Base (The rs ds gs))
    ascript fc rho delta gamma ty syn
       = do (ty ** tm) <- typeCheck delta ty
            res <- ascript fc rho delta gamma tm syn
            pure (ty ** res)

  export
  ascript : {t     : Base}
         -> {e     : Expr}
         -> {rs    : List Ty.Role}
         -> {ds,gs : List Ty.Base}
         -> (fc    : FileContext)
         -> (rho   : Context Ty.Role rs)
         -> (delta : Context Ty.Base ds)
         -> (gamma : Context Ty.Base gs)
         -> (ty    : Ty ds t)
         -> (syn   : Expr e)
                  -> Ola (The rs ds gs t)

  ascript {t = (ARRAY type 0)} fc rho delta gamma (TyArray tmType 0) (Null fc')
    = pure (T (TyArray tmType 0) ArrayEmpty)

  ascript {t = (ARRAY type (S k))} fc rho delta gamma (TyArray tmType (S k)) (Null fc')
    = mismatchAt fc (ARRAY type (S k)) (ARRAY type Z)

  ascript {t = (UNION a b)} fc rho delta gamma (TyUnion tmA tmB) (Left  fc' l)
    = do (tyL' ** l') <- check rho delta gamma l
         Refl <- compare fc a tyL'
         pure (T (TyUnion tmA tmB) (Left l'))

  ascript {t = (UNION a b)} fc rho delta gamma (TyUnion tmA tmB) (Right fc' r)
    = do (tyR' ** r') <- check rho delta gamma r
         Refl <- compare fc b tyR'
         pure (T (TyUnion tmA tmB) (Right r'))


  ascript {t = t} fc rho delta gamma ty expr
    = do (ty' ** e) <- check rho delta gamma expr
         Refl <- compare fc t ty'
         pure (T ty e)

export
ascriptReflect : {e     : Expr}
              -> {rs    : List Ty.Role}
              -> {ds,gs : List Ty.Base}
              -> (rho   : Context Ty.Role rs)
              -> (delta : Context Ty.Base ds)
              -> (gamma : Context Ty.Base gs)
              -> (syn   : Expr e)
                       -> Ola (DPair Base (The rs ds gs))
ascriptReflect rho delta gamma syn
  = do (ty ** expr) <- check rho delta gamma syn
       tm <- typeReflect delta ty
       pure (_ ** T tm expr)


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
