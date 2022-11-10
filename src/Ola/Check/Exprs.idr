||| Type-checker for expressions.
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
||| [ NOTE ]
|||
||| There is not enough information to type sums (or empty arrays) in
||| their introduction forms.  We will type them at binder locations,
||| ascriptions, as arguments, and for empty arrays also /in situ/ in
||| a cons cell.
module Ola.Check.Exprs

import Toolkit.Data.Location
import Toolkit.Data.DVect

import Ola.Types
import Ola.Core

import Ola.Raw.AST
import Ola.Raw.Types
import Ola.Raw.Exprs

import Ola.Check.Common
import Ola.Check.Types

import        Ola.Terms.Vars
import public Ola.Terms.Builtins
import        Ola.Terms.Types
import        Ola.Terms.Exprs

%default total


mutual
  checkBinOpB : {a,b   : EXPR}
             -> {rs    : List Ty.Role}
             -> {ds,gs : List Ty.Base}
             -> (env   : Env rs ds gs)
             -> (fc    : FileContext)
             -> (synA  : Expr a)
             -> (synb  : Expr b)
             -> (k     : BinOpBoolKind)
                      -> Ola (Expr rs ds gs BOOL)
  checkBinOpB env fc l r k
    = do T tyTm l <- check fc env TyBool l
         T tyTm r <- check fc env TyBool r

         pure (Builtin (BinOpBool k) [l, r])

  checkBinOpI : {a,b   : EXPR}
             -> {rs    : List Ty.Role}
             -> {ds,gs : List Ty.Base}
             -> (env   : Env rs ds gs)
             -> (fc    : FileContext)
             -> (synA  : Expr a)
             -> (synb  : Expr b)
             -> (k     : BinOpIntKind)
                      -> Ola (Expr rs ds gs INT)
  checkBinOpI env fc l r k
    = do T tyTm l <- check fc env TyInt l
         T tyTm r <- check fc env TyInt r

         pure (Builtin (BinOpInt k) [l, r])


  checkCmp : {a,b   : EXPR}
          -> {rs    : List Ty.Role}
          -> {ds,gs : List Ty.Base}
          -> (env   : Env rs ds gs)
          -> (fc    : FileContext)
          -> (synA  : Expr a)
          -> (synb  : Expr b)
          -> (k     : BinOpCmpKind)
                   -> Ola (Expr rs ds gs BOOL)
  checkCmp env fc l r k
    = do (tyL ** l) <- synth env l
         (tyR ** r) <- synth env r

         Refl <- compare fc tyL tyR

         maybe (throwAt fc Uncomparable)
               (\prf => pure (Builtin (Cmp prf k) [l, r]))
               (cmpTy tyL)

  export
  synth : {e     : EXPR}
       -> {rs    : List Ty.Role}
       -> {ds,gs : List Ty.Base}
       -> (env   : Env rs ds gs)
       -> (syn   : Expr e)
                -> Ola (DPair Ty.Base (Expr rs ds gs))
  synth env (Var ref prf)
    = do (ty ** idx) <- lookup (gamma env) ref
         pure (_ ** Var idx)

  synth env (LetTy fc ref st ty val scope)
    = do (tyVal ** T tyTmVal val) <- check fc env ty val

         case st of
           HEAP
             => do (tyS ** scope) <- synth (extend env ref (REF tyVal)) scope

                   pure (_ ** Let (TyRef tyTmVal) (Builtin Alloc [val]) scope)
           STACK
             => do (tyS ** scope) <- synth (extend env ref tyVal) scope

                   pure (_ ** Let tyTmVal val scope)


  synth env (Let fc ref st val scope)
    = do (tyVal ** T tyTmVal val) <- synthReflect env val

         case st of
           HEAP
             => do (tyS ** scope) <- synth (extend env ref (REF tyVal)) scope

                   pure (_ ** Let (TyRef tyTmVal) (Builtin Alloc [val]) scope)
           STACK
             => do (tyS ** scope) <- synth (extend env ref tyVal) scope

                   pure (_ ** Let tyTmVal val scope)


  -- ## Builtins

  -- ### Constants
  synth env (Const fc UNIT v) = pure (_ ** Builtin  U    Nil)
  synth env (Const fc CHAR v) = pure (_ ** Builtin (C v) Nil)
  synth env (Const fc STR v)  = pure (_ ** Builtin (S v) Nil)
  synth env (Const fc INT v)  = pure (_ ** Builtin (I v) Nil)
  synth env (Const fc BOOL v) = pure (_ ** Builtin (B v) Nil)

  -- [ NOTE ] @TODO The builtins could be factored out better.

  -- ### Boolean ops
  synth env (OpBin fc AND l r)
    = pure (_ ** !(checkBinOpB env fc l r AND))

  synth env (OpBin fc OR  l r)
    = pure (_ ** !(checkBinOpB env fc l r OR))

  synth env (OpUn  fc NOT o)
    = do T tyTm l <- check fc env TyBool o
         pure ( _ ** Builtin Not [l])

  -- ### Comparators
  synth env (OpBin fc LT l r)
    = pure (_ ** !(checkCmp env fc l r LT))

  synth env (OpBin fc LTE l r)
     = pure (_ ** !(checkCmp env fc l r LTE))

  synth env (OpBin fc EQ l r)
    = pure (_ ** !(checkCmp env fc l r EQ))

  synth env (OpBin fc GT l r)
      = pure (_ ** !(checkCmp env fc l r GT))

  synth env (OpBin fc GTE l r)
    = pure (_ ** !(checkCmp env fc l r GTE))

  -- ### Maths
  synth env (OpBin fc ADD l r)
    = pure (_ ** !(checkBinOpI env fc l r ADD))

  synth env (OpBin fc SUB l r)
    = pure (_ ** !(checkBinOpI env fc l r SUB))

  synth env (OpBin fc MUL l r)
    = pure (_ ** !(checkBinOpI env fc l r MUL))

  synth env (OpBin fc DIV l r)
    = pure (_ ** !(checkBinOpI env fc l r DIV))

  -- ### Strings & Chars
  synth env (OpBin fc STRCONS h t)
    = do T tyH h <- check fc env TyChar h
         T tyT t <- check fc env TyStr  t
         pure (_ ** Builtin (StrOp Cons) [h,t])

  synth env (OpUn fc SIZE o)
    = do T tyTm t <- check fc env TyStr o
         pure (_ ** Builtin (StrOp Length) [t])

  synth env (OpUn fc ORD o)
    = do T tyTm t <- check fc env TyChar o
         pure (_ ** Builtin (CharOp Ord) [t])

  synth env (OpUn fc CHR o)
    = do T tyTm l <- check fc env TyInt o
         pure (_ ** Builtin (CharOp Chr) [l])

  synth env (OpUn fc STRO o)
    = do T tyTm l <- check fc env TyChar o
         pure (_ ** Builtin (CharOp Singleton) [l])

  synth env (OpUn fc TOSTR l)
    = do (ty ** l) <- synth env l

         maybe (throwAt fc Uncomparable)
               (\prf => pure (_ ** Builtin (ToString prf) [l]))
               (cmpTy ty)

  -- ### Memory
  synth env (OpBin fc MUT ptr val)
    = do (tyV ** val) <- synth env val

         (REF t ** ptr) <- synth env ptr
           | (ty ** _) => mismatchAt fc (REF tyV) (ty)

         Refl <- compare fc tyV t

         pure (_ ** Builtin Mutate [ptr, val])

  synth env (OpUn fc FETCH ptr)
    = do (REF t ** tm) <- synth env ptr
           | (ty ** tm) => throwAt fc (RefExpected ty)

         pure (_ ** Builtin Fetch [tm])

  -- ### Files
  synth env (OpUn fc (OPEN k m) o)
    = do T _ tm <- check fc env TyStr o

         pure (_ ** Builtin (Open k m) [tm])

  synth env (OpBin fc WRITE h s)
    = do (HANDLE k ** h) <- synth env h
           | (ty ** _) =>  throwAt fc (HandleExpected ty)

         T _ s <- check fc env TyStr s

         pure (_ ** Builtin WriteLn [h, s])


  synth env (OpUn fc READ o)
    = do (HANDLE k ** h) <- synth env o
           | (ty ** _) =>  throwAt fc (HandleExpected ty)

         pure (_ ** Builtin ReadLn [h])

  synth env (OpUn fc CLOSE o)
    = do (HANDLE k ** h) <- synth env o
           | (ty ** _) => throwAt fc (HandleExpected ty)

         pure (_ ** Builtin Close [h])

  -- ### Side Effects
  synth env (OpUn fc PRINT s)
    = do T _ s <- check fc env TyStr s
         pure (_ ** Builtin Print [s])

  -- ## Arrays
  synth env (ArrayEmpty fc)
    = unknown fc

  synth env (ArrayCons fc head (ArrayEmpty _))
    = do (tyH ** head) <- synth env head
         -- Could do a check but we don't need to.
         pure (_ ** ArrayCons head ArrayEmpty)

  synth env (ArrayCons fc head tail)
    = do (tyH ** head) <- synth env head
         (ARRAY ty' n ** tail) <- synth env tail
           | (ty ** _) => throwAt fc (ArrayExpected ty)

         Refl <- compare fc tyH ty'

         pure (_ ** ArrayCons head tail)

  synth env (Index fc idx tm)
    = do T tyTm idx <- check fc env TyInt idx

         (ARRAY ty m ** tm) <- synth env tm
           | (ty ** _) => throwAt fc (ArrayExpected ty)

         pure (_ ** Index idx tm)

  synth env (Slice fc st ed tm)
    = do T tyTm st <- check fc env (TyInt) st
         T tyTm ed <- check fc env (TyInt) ed
         T tyTm tm <- check fc env (TyStr) tm
         pure (_ ** Builtin (StrOp Slice) [st, ed, tm])


  -- ## Pairs
  synth env (MkPair fc fst snd)
    = do (tyA ** tmA) <- synth env fst
         (tyB ** tmB) <- synth env snd

         pure (_ ** Pair tmA tmB)

  synth env (Split fc c f s scope)
    = do (PAIR tyF tyS ** c) <- synth env c
           | (ty ** _) => throwAt fc (PairExpected ty)
         (_ ** scope) <- synth (Gamma.extend
                               (Gamma.extend env f tyF)
                                                 s tyS)
                               scope

         pure (_ ** Split c scope)

  -- ## Unions
  synth env (Match fc cond l scopeL r scopeR)
    = do (UNION tyL tyR ** c) <- synth env cond
           | (ty ** _) => throwAt fc (UnionExpected ty)

         -- left
         (tyL' ** scopeL) <- synth (Gamma.extend env l tyL) scopeL

         -- right
         (tyR' ** scopeR) <- synth (Gamma.extend env r tyR) scopeR

         Refl <- compare fc tyL' tyR'

         pure (_ ** Match c scopeL scopeR)

  synth env (Left fc tm)
    = unknown fc
  synth env (Right fc tm)
    = unknown fc

  -- ## Ascriptions
  synth env (The fc ty tm)
    = do (_ ** T ty tm) <- check fc env ty tm
         pure (_ ** tm)

  -- ## Control Flows
  synth env (Cond fc c t f)
    = do T _ c <- check fc env TyBool c

         (tyT ** tt) <- synth env t

         (tyF ** ff) <- synth env f

         Refl <- compare fc tyT tyF

         pure (_ ** Cond c tt ff)

  synth env (Seq fc this that)
    = do T _ this <- check fc env TyUnit this
         (ty ** that) <- synth env that

         pure (_ ** Seq this that)

  synth env (Loop fc scope cond)
    = do (ty ** scope) <- synth env scope
         T _ cond <- check fc env TyBool cond

         pure (_ ** Loop scope cond)

  synth env (Call fc fun prf argz)
    = do (FUNC argTys _ ** fun) <- synth env fun
           | (ty ** _) => throwAt fc (FunctionExpected ty)
         args' <- args fc argTys argz

         pure (_ ** Call fun args')

    where size : Vect.Quantifiers.All.All Expr as
              -> Nat
          size Nil = Z
          size (x::xs) = S (size xs)

          args : {as   : Vect n EXPR}
              -> (fc   : FileContext)
              -> (tys  : List Ty.Base)
              -> (args : All Expr as)
                      -> Ola (DList Ty.Base
                                    (Expr rs ds gs)
                                    tys)
          args _ [] []
            = pure Nil

          args fc [] (elem :: rest)

            = throwAt fc (RedundantArgs (size (elem :: rest)))

          args fc (x :: xs) []
            = throwAt fc (ArgsExpected (x::xs))

          args fc (x :: xs) (tm' :: tms)
            = do (ty ** tm) <- synth env tm'

                 let Val (getFC q) = getFC tm'
                 Refl <- compare (getFC q) x ty

                 rest <- args fc xs tms

                 pure (tm :: rest)

  namespace View
    export
    check : {e     : EXPR}
         -> {rs    : List Ty.Role}
         -> {ds,gs : List Ty.Base}
         -> (fc    : FileContext)
         -> (env   : Env rs ds gs)
         -> (ty    : Ty t)
         -> (syn   : Expr e)
                  -> Ola (DPair Base (The rs ds gs))
    check fc env ty syn
       = do (ty ** tm) <- synth (delta env) ty
            res <- check fc env tm syn
            pure (ty ** res)

  export
  check : {t     : Base}
       -> {e     : EXPR}
       -> {rs    : List Ty.Role}
       -> {ds,gs : List Ty.Base}
       -> (fc    : FileContext)
       -> (env   : Env rs ds gs)
       -> (ty    : Ty ds t)
       -> (syn   : Expr e)
                -> Ola (The rs ds gs t)

  check {t = (ARRAY type 0)} fc env (TyArray tmType 0) (ArrayEmpty fc')
    = pure (T (TyArray tmType 0) ArrayEmpty)

  check {t = (ARRAY type (S k))} fc env (TyArray tmType (S k)) (ArrayEmpty fc')
    = mismatchAt fc (ARRAY type (S k)) (ARRAY type Z)

  check {t = (UNION a b)} fc env (TyUnion tmA tmB) (Left  fc' l)
    = do (tyL' ** l') <- synth env l
         Refl <- compare fc a tyL'
         pure (T (TyUnion tmA tmB) (Left l'))

  check {t = (UNION a b)} fc env (TyUnion tmA tmB) (Right fc' r)
    = do (tyR' ** r') <- synth env r
         Refl <- compare fc b tyR'
         pure (T (TyUnion tmA tmB) (Right r'))


  check {t = t} fc env ty expr
    = do (ty' ** e) <- synth env expr
         Refl <- compare fc t ty'
         pure (T ty e)

  namespace Reflect
    export
    synthReflect : {e     : EXPR}
                -> {rs    : List Ty.Role}
                -> {ds,gs : List Ty.Base}
                -> (env   : Env rs ds gs)
                -> (syn   : Expr e)
                         -> Ola (DPair Base (The rs ds gs))
    synthReflect env syn
      = do (ty ** expr) <- Exprs.synth env syn
           tm <- reflect (delta env) ty
           pure (_ ** T tm expr)

namespace Raw
  export
  synth : {rs    : List Ty.Role}
       -> {ds,gs : List Ty.Base}
       -> (env   : Env rs ds gs)
       -> (syn   : EXPR)
                -> Ola (DPair Ty.Base (Expr rs ds gs))
  synth env e
    = synth env (toExpr e)

-- [ EOF ]
