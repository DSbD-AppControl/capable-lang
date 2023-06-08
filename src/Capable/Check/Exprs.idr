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
|||
module Capable.Check.Exprs

import Toolkit.Data.Location
import Toolkit.Data.DList
import Toolkit.Data.DVect
import Toolkit.Data.Vect.Extra

import Capable.Types
import Capable.Core

import Capable.Raw.AST
import Capable.Raw.Role
import Capable.Raw.Types
import Capable.Raw.Exprs

import Capable.Check.Common
import Capable.Check.Types

import        Capable.Terms.Vars
import public Capable.Terms.Builtins
import        Capable.Terms.Types
import        Capable.Terms.Exprs

import Debug.Trace

%default total

export
isElem : (fc,fc' : FileContext)
      -> (s      : String)
      -> (xs     : List (String, Base))
                -> Capable $ DPair Base (\x => Elem (s,x) xs)
isElem fc fc' s []
  = throwAt fc (NotBound (MkRef fc' s))

isElem fc fc' s ((s',x) :: xs) with (decEq s s')
  isElem fc fc' s ((s,x) :: xs) | (Yes Refl) = pure (x ** Here)
  isElem fc fc' s ((s',x) :: xs) | (No contra)
    = do (x' ** prf) <- isElem fc fc' s xs
         pure (x' ** There prf)

mutual
  checkBinOpB : {a,b      : EXPR}
             -> {rs       : List Ty.Role}
             -> {ds,ls : List Ty.Base} -> { gs : List Ty.Method }
             -> {ss       : List Ty.Session}
             -> (env      : Env rs ds ss gs ls)
             -> (fc       : FileContext)
             -> (synA     : Expr a)
             -> (synb     : Expr b)
             -> (k        : BinOpBoolKind)
                         -> Capable (Expr rs ds ss gs ls BOOL)
  checkBinOpB env fc l r k
    = do T tyTm l <- check fc env TyBool l
         T tyTm r <- check fc env TyBool r

         pure (Builtin (BinOpBool k) [l, r])

  checkBinOpI : {a,b      : EXPR}
             -> {rs       : List Ty.Role}
             -> {ds,ls : List Ty.Base} -> { gs : List Ty.Method }
             -> {ss       : List Ty.Session}
             -> (env      : Env rs ds ss gs ls)
             -> (fc       : FileContext)
             -> (synA     : Expr a)
             -> (synb     : Expr b)
             -> (k        : BinOpIntKind)
                         -> Capable (Expr rs ds ss gs ls INT)
  checkBinOpI env fc l r k
    = do T tyTm l <- check fc env TyInt l
         T tyTm r <- check fc env TyInt r

         pure (Builtin (BinOpInt k) [l, r])


  checkCmp : {a,b      : EXPR}
          -> {rs       : List Ty.Role}
          -> {ds,ls : List Ty.Base} -> { gs : List Ty.Method }
          -> {ss       : List Ty.Session}
          -> (env      : Env rs ds ss gs ls)
          -> (fc       : FileContext)
          -> (synA     : Expr a)
          -> (synb     : Expr b)
          -> (k        : BinOpCmpKind)
                      -> Capable (Expr rs ds ss gs ls BOOL)
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
       -> {ds,ls : List Ty.Base}
       -> {gs    : List Ty.Method }
       -> {ss    : List Ty.Session}
       -> (env   : Env rs ds ss gs ls)
       -> (syn   : Expr e)
                -> Capable (DPair Ty.Base (Expr rs ds ss gs ls))

  synth env (Hole ref prf) = unknown (span ref)

  synth env (Var ref prf)
      = do (ty ** idx) <- Lambda.lookup env ref
           pure (ty ** Var idx)

--    = case !(lookup env ref) of
--        (_ ** IsLocal  idx) => pure (_ ** VarL idx)
--        (_ ** IsGlobal idx) => pure (_ ** VarG idx)


  synth env (LetTy fc ref st ty val scope)
    = do (tyVal ** T tyTmVal val) <- check fc env ty val

         case st of
           HEAP
             => do (tyS ** scope) <- synth (Lambda.extend env ref (REF tyVal)) scope

                   pure (_ ** Let (TyRef tyTmVal) (Builtin Alloc [val]) scope)
           STACK
             => do (tyS ** scope) <- synth (Lambda.extend env ref tyVal) scope

                   pure (_ ** Let tyTmVal val scope)


  synth env (Let fc ref st val scope)
    = do (tyVal ** T tyTmVal val) <- synthReflect env val

         case st of
           HEAP
             => do (tyS ** scope) <- synth (Lambda.extend env ref (REF tyVal)) scope

                   pure (_ ** Let (TyRef tyTmVal) (Builtin Alloc [val]) scope)
           STACK
             => do (tyS ** scope) <- synth (Lambda.extend env ref tyVal) scope

                   pure (_ ** Let tyTmVal val scope)

  synth env (Split fc this val scope)
    = do (TUPLE (f::s::ts) ** v) <- synth env val
           | (tyV ** _) => throwAt fc (PairExpected tyV)

         envExt <- zip env this (f::s::ts)

         (_ ** rest) <- synth envExt scope

         pure (_ ** Split v rest)


    where zip : (env : Env rs ds ss gs ls)
             -> (xs : List String)
             -> (ys : Vect m Base)
                   -> Capable (Env rs ds ss gs (Extra.toList ys ++ ls))
          zip env [] [] = pure env
          zip env [] (x :: xs)
            = throwAt fc (PatternsMissing (Extra.toList $ x::xs))

          zip env (x :: xs) []
            = throwAt fc (RedundantPatterns (x::xs))

          zip env (x :: xs) (y :: ys)
            = do rest <- zip env xs ys
                 pure (Lambda.extend rest x y)

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
  synth env (OpUn fc POPEN2 o)
    = do T _ tm <- check fc env TyStr o

         pure (_ ** Builtin POpen2 [tm])

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

  -- ## Lists

  synth env (MkList fc Empty [])
    = unknown fc

  synth env (MkList fc (Next Empty) (x :: []))
    = do (ty ** x) <- synth env x
         pure (_ ** MkList [x])

  synth env (MkList fc (Next (Next z)) (x :: (y :: w)))
    = do (ty ** x) <- synth env x
         (LIST ty' ** MkList xs) <- synth env (MkList fc (Next z) (y::w))
           | (ty' ** _) => mismatch (LIST ty) ty'

         Refl <- compare fc ty ty'

         pure (_ ** MkList (x::xs))


  synth env (SetL fc idx tm val)
    = do idx <- check fc env INT idx

         (ty ** val) <- synth env val

         tm <- check fc env (LIST ty) tm

         pure (_ ** SetL idx tm val)

  synth env (GetL fc idx tm)
    = do idx <- check fc env INT idx

         (LIST ty ** tm) <- synth env tm
           | (ty ** _) => throwAt fc (ListExpected ty)

         pure (_ ** GetL idx tm)

  -- ## Vectors
  synth env (MkVect fc Empty [])
    = unknown fc

  synth env (MkVect fc (Next Empty) (x :: []))
    = do (ty ** x) <- synth env x
         pure (_ ** MkVect [x])

  synth env (MkVect fc (Next (Next z)) (x :: (y :: w)))
    = do (ty ** x) <- synth env x
         (VECTOR m ty' ** MkVect xs) <- synth env (MkVect fc (Next z) (y::w))
           | (ty ** _) => throwAt fc (VectorExpected ty)

         Refl <- compare fc ty m

         pure (_ ** MkVect (x::xs))

  synth env (SetV fc idx tm val)
    = do (ty ** val) <- synth env val

         (VECTOR ty' m ** tm) <- synth env tm
           | (ty ** _) => throwAt fc (VectorExpected ty)

         Refl <- compare fc ty ty'

         ifThenElse (idx < 0)
                    (throwAt fc NatExpected)
                    (maybe (throwAt fc (OOB (cast idx) m))
                           (\idx => pure (_ ** SetV idx tm val))
                           (natToFin (cast idx) m))

  synth env (GetV fc idx tm)
    = do (VECTOR ty' m ** tm) <- synth env tm
           | (ty ** _) => throwAt fc (VectorExpected ty)

         ifThenElse (idx < 0)
                    (throwAt fc NatExpected)
                    (maybe (throwAt fc (OOB (cast idx) m))
                           (\idx => pure (_ ** GetV idx tm))
                           (natToFin (cast idx) m))

  synth env (Slice fc st ed tm)
    = do T tyTm st <- check fc env (TyInt) st
         T tyTm ed <- check fc env (TyInt) ed
         T tyTm tm <- check fc env (TyStr) tm
         pure (_ ** Builtin (StrOp Slice) [st, ed, tm])


  -- ## Pairs
  synth env (MkTuple fc prf ts)
    = do (_ ** (tyA::tyB::tys) ** (a::b::tms)) <- args ts
           | _ => throwAt fc Unknown
         pure (_ ** Tuple (a::b::tms))

    where args : {as' : _} -> Vect.Quantifiers.All.All Expr as'
              -> Capable (DPair Nat
                            (\n => DPair (Vect n Base)
                                         (DVect Base (Expr rs ds ss gs ls) n)))
          args [] = pure (_ ** _ ** Nil)

          args (l :: y)
            = do (ty ** tm) <- synth env l
                 (n ** tys ** tms) <- args y
                 pure (S n ** ty::tys ** tm::tms)

  synth env (GetT fc loc tup)
    = do if loc < 0
          then throwAt fc (NatExpected)
          else do (TUPLE ts ** tm) <- synth env tup
                    | (ty ** _) => throwAt fc (PairExpected ty)
                  maybe (throwAt fc (OOB (cast loc) (length ts)))
                        (\idx => pure (_ ** GetT tm idx))
                        (finFromVect (cast loc) ts)

  synth env (SetT fc loc tup v)
    = do if loc < 0
           then throwAt fc (NatExpected)
           else do (TUPLE ts ** tm) <- synth env tup
                      | (ty ** _) => throwAt fc (PairExpected ty)

                   maybe (throwAt fc (OOB (cast loc) (length ts)))
                         (\idx => do (tyV ** tmV) <- synth env v
                                     Refl <- compare fc (index idx ts) tyV
                                     pure (_ ** SetT tm idx tmV))
                         (finFromVect (cast loc) ts)

  -- ## Records
  synth env (Record fc prf (f::fs))
    = do (_ ** f) <- field f

         (_ ** fs) <- fields fs

         pure (_ ** Record (f :: fs))

    where field : (giv : Field sco)
                      -> Capable (DPair (String,Base) (Field rs ds ss gs ls))
          field (F fc s e)
            = do (t ** tm) <- synth env e
                 pure (_ ** F s tm)

          fields : Vect.Quantifiers.All.All Field as'
                -> Capable (DPair (List (String, Base))
                              (DList (String,Base)
                                     (Field rs ds ss gs ls)))
          fields Nil
            = pure (_ ** Nil)

          fields (f::fs)
            = do (_ ** f) <- field f

                 (_ ** fs) <- fields fs
                 pure (_ ** f::fs)

  synth env (GetR fc loc tup)
    = do (RECORD (t:::ts) ** tm) <- synth env tup
            | (ty ** _) => throwAt fc (RecordExpected ty)

         (ty ** loc) <- isElem fc fc loc (t::ts)

         pure (_ ** GetR tm loc)


  synth env (SetR fc loc tup v)
    = do (RECORD (t:::ts) ** tm) <- synth env tup
           | (ty ** _) => throwAt fc (RecordExpected ty)

         (ty ** loc) <- isElem fc fc loc (t::ts)

         (tyV ** tmV) <- synth env v

         Refl <- compare fc ty tyV

         pure (_ ** SetR tm loc tmV)


  -- ## Unions
  synth env (Match fc cond prf (C fcC s sc c::cs))
    = do (UNION ((s',cTy) ::: tys) ** cond) <- synth env cond
           | (ty ** _) => throwAt fc (UnionExpected ty)

         (rTy ** cTm) <- case' fcC s' s sc cTy c

         cTms <- cases fc rTy tys cs

         pure (_ ** Match cond (cTm :: cTms))

    where case' : {sco : _}
               -> (fc  : FileContext)
               -> (s'  : String)
               -> (s   : String)
               -> (sc  : String)
               -> (cTy : Base)
               -> (giv : Expr sco)
                      -> Capable (DPair Base (\ret => Case rs ds ss gs ls ret (s',cTy)))
          case' fc s' str sc cTy giv
            = do Refl <- embedAt fc (WrongLabel s' str) (decEq s' str)
                 (rTy ** cTm) <- synth (Lambda.extend env sc cTy) giv
                 pure (rTy ** C s' cTm)

          cases : (fc : FileContext)
               -> (ret : Base)
               -> (exp : List (String, Base))
               -> Vect.Quantifiers.All.All Case as'
               -> Capable (DList (String,Base)
                             (Case rs ds ss gs ls ret)
                             exp)
          cases _ ret Nil Nil
            = pure Nil

          cases fc ret Nil cs
            = throwAt fc (RedundantCases (flattern cs))

          cases fc ret es Nil
            = throwAt fc (CasesMissing es)

          cases fc ret ((se,te)::exp) (C fcC sg sc c::cs)

            = do (rTy' ** c') <- case' fcC se sg sc te c
                 Refl <- compare fcC ret rTy'

                 rest <- cases fc ret exp cs
                 pure (c'::rest)


  synth env (Tag fc _ _)
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

  synth env (ForEach fc (MkRef fc s) R cond scope)
    = case !(synth env cond) of
        (VECTOR ty sl ** c)
          => do scope <- check fc (Lambda.extend env s ty) UNIT scope
                pure (_ ** ForEach c V scope)

        (LIST ty ** c)
          => do scope <- check fc (Lambda.extend env s ty) UNIT scope
                pure (_ ** ForEach c L scope)

        (ty ** _) => throwAt fc (IterableExpected ty)

  synth env (Loop fc scope cond)
    = do (ty ** scope) <- synth env scope
         T _ cond <- check fc env TyBool cond

         pure (_ ** Loop scope cond)

  synth env (Call fc (MkRef fc s) R prf argz)
    = do (FUNC argTys _ ** idx) <- Gamma.lookup env (MkRef fc s)
         --(FUNC argTys _ ** fun) <- synth env fun
           | (ty ** _) => throwAt fc (FunctionExpected ty)
         args' <- args fc argTys argz

         pure (_ ** Call idx args')

    where size : Vect.Quantifiers.All.All Expr as
              -> Nat
          size Nil = Z
          size (x::xs) = S (size xs)

          args : {as   : Vect n EXPR}
              -> (fc   : FileContext)
              -> (tys  : List Ty.Base)
              -> (args : Vect.Quantifiers.All.All Expr as)
                      -> Capable (DList Ty.Base
                                    (Expr rs ds ss gs ls)
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

  synth env (Run fc (MkRef fc s) R pA argz pV vs)
    = do (SESH ctxt whom prot argTys _ ** idx) <- Gamma.lookup env (MkRef fc s)
         --(FUNC argTys _ ** fun) <- synth env fun
           | (ty ** _) => throwAt fc (SessionExpected ty)

         let (R pz proles) = hasRoles prot

         args' <- args fc argTys argz

         asgns <- assignments ctxt pz vs
         pure (_ ** Run idx
                        asgns
                        proles
                        args')

    where size : Vect.Quantifiers.All.All Expr as
              -> Nat
          size Nil = Z
          size (x::xs) = S (size xs)

          args : {as   : Vect n EXPR}
              -> (fc   : FileContext)
              -> (tys  : List Ty.Base)
              -> (args : Vect.Quantifiers.All.All Expr as)
                      -> Capable (DList Ty.Base
                                    (Expr rs ds ss gs ls)
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

          getNames : Vect.Quantifiers.All.All Val qs -> List String
          getNames Nil = Nil
          getNames (V fc (R s') _ :: rest) = s' :: getNames rest

          assignments : {vs   : Vect n (AST VAL)}
                     -> (ctxt : Context Role roles)
                     -> (prs  : Roles roles ps)
                     -> (vals : Vect.Quantifiers.All.All Val vs)
                     -> Capable (Assignments roles rs ds ss gs ls p prs)
          assignments _ [] []
            = pure Empty

          assignments _ [] (x :: y)
            = throwAt fc (RedundantRoles $ getNames (x::y))

          assignments renv (r :: rz) Nil
            = do let qq = mapToList (reflect renv) (r :: rz)
                 throwAt fc (RolesExpected qq)

          assignments renv (r :: rz) (V fc' (R r') v::vs)
            = do let r'' = reflect renv r
                 Refl <- embedAt fc' (MismatchRole (MkRef fc' r') (MkRef fc' r''))
                                     (decEq r'' r')

                 T _ tm <- check fc' env TyStr v
                 rest <- assignments renv rz vs
                 pure (KV r tm rest)

  namespace View
    export
    check : {e        : EXPR}
         -> {rs       : List Ty.Role}
         -> {ds,ls : List Ty.Base} -> { gs : List Ty.Method }
         -> {ss       : List Ty.Session}
         -> (fc       : FileContext)
         -> (env      : Env rs ds ss gs ls)
         -> (ty       : Ty t)
         -> (syn      : Expr e)
                     -> Capable (DPair Base (The rs ds ss gs ls))
    check fc env ty syn
       = do (ty ** tm) <- synth (delta env) ty
            res <- check fc env tm syn
            pure (ty ** res)

  export
  check : {t        : Base}
       -> {e        : EXPR}
       -> {rs       : List Ty.Role}
       -> {ds,ls : List Ty.Base} -> { gs : List Ty.Method }
       -> {ss       : List Ty.Session}
       -> (fc       : FileContext)
       -> (env      : Env rs ds ss gs ls)
       -> (ty       : Ty ds t)
       -> (syn      : Expr e)
                   -> Capable (The rs ds ss gs ls t)

  check {t = (LIST type)} fc env tyTm (MkList fc' prf [])
    = pure (T tyTm (MkList Nil))

  check {t = (VECTOR type 0)} fc env tyTm (MkVect fc' prf [])
    = pure (T tyTm (MkVect Nil))

  check {t = (VECTOR type (S k))} fc env tyTm (MkVect fc' prf [])
    = mismatchAt fc (VECTOR type (S k)) (VECTOR type Z)

  check {t = (UNION (a:::as))} fc env tyTm (Tag fc' s l)
    = do (ty ** loc) <- isElem fc fc' s (a::as)
         (ty' ** tm) <- synth env l

         Refl <- compare fc' ty ty'
         pure (T tyTm (Tag s tm loc))

  check {t = t} fc env ty (Hole (MkRef fc' s) R)
    = showHoleExit (lambda env) s t
         -- pure (T ty (Hole fc ref))
         -- @TODO add infrastructure to collect all the holes, and then report.

  check {t = t} fc env ty expr
    = do (ty' ** e) <- synth env expr
         Refl <- compare fc t ty'
         pure (T ty e)

  namespace Reflect
    export
    synthReflect : {e        : EXPR}
                -> {rs       : List Ty.Role}
                -> {ds,ls : List Ty.Base} -> { gs : List Ty.Method }
                -> {ss       : List Ty.Session}
                -> (env      : Env rs ds ss gs ls)
                -> (syn      : Expr e)
                            -> Capable (DPair Base (The rs ds ss gs ls))
    synthReflect env syn
      = do (ty ** expr) <- Exprs.synth env syn
           tm <- reflect (delta env) ty
           pure (_ ** T tm expr)

    export
    check : {e        : EXPR}
         -> {rs       : List Ty.Role}
         -> {ds,ls : List Ty.Base} -> { gs : List Ty.Method }
         -> {ss       : List Ty.Session}
         -> (fc       : FileContext)
         -> (env      : Env rs ds ss gs ls)
         -> (ty       : Base)
         -> (syn      : Expr e)
                     -> Capable (Expr rs ds ss gs ls ty)
    check fc env ty syn
      = do (ty' ** expr) <- Exprs.synth env syn
           Refl <- compare fc ty ty'
           pure expr

namespace Raw
  export
  synth : {rs       : List Ty.Role}
       -> {ds,ls : List Ty.Base} -> { gs : List Ty.Method }
       -> {ss       : List Ty.Session}
       -> (env      : Env rs ds ss gs ls)
       -> (syn      : EXPR)
                   -> Capable (DPair Ty.Base (Expr rs ds ss gs ls))
  synth env e
    = synth env (toExpr e)

-- [ EOF ]
