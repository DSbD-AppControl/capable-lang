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

import Capable.State

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
             -> (st       : State)
             -> (env      : Env rs ds ss gs ls)
             -> (fc       : FileContext)
             -> (synA     : Expr a)
             -> (synb     : Expr b)
             -> (k        : BinOpBoolKind)
                         -> Capable (State, Expr rs ds ss gs ls BOOL)
  checkBinOpB st env fc l r k
    = do (st,T tyTm l) <- check st fc env TyBool l
         (st,T tyTm r) <- check st fc env TyBool r

         pure (st, Builtin (BinOpBool k) [l, r])

  checkBinOpI : {a,b      : EXPR}
             -> {rs       : List Ty.Role}
             -> {ds,ls : List Ty.Base} -> { gs : List Ty.Method }
             -> {ss       : List Ty.Session}
             -> (st       : State)
             -> (env      : Env rs ds ss gs ls)
             -> (fc       : FileContext)
             -> (synA     : Expr a)
             -> (synb     : Expr b)
             -> (k        : BinOpIntKind)
                         -> Capable (State, Expr rs ds ss gs ls INT)
  checkBinOpI st env fc l r k
    = do (st, T tyTm l) <- check st fc env TyInt l
         (st, T tyTm r) <- check st fc env TyInt r

         pure (st, Builtin (BinOpInt k) [l, r])


  checkCmp : {a,b      : EXPR}
          -> {rs       : List Ty.Role}
          -> {ds,ls : List Ty.Base}
          -> { gs : List Ty.Method }
          -> {ss       : List Ty.Session}
          -> (st       : State)
          -> (env      : Env rs ds ss gs ls)
          -> (fc       : FileContext)
          -> (synA     : Expr a)
          -> (synb     : Expr b)
          -> (k        : BinOpCmpKind)
                      -> Capable (State, Expr rs ds ss gs ls BOOL)
  checkCmp st env fc l r k
    = do (st, (tyL ** l)) <- synth st env l
         (st, (tyR ** r)) <- synth st env r

         Refl <- compare fc tyL tyR

         maybe (throwAt fc Uncomparable)
               (\prf => pure (st, Builtin (Cmp prf k) [l, r]))
               (cmpTy tyL)

  export
  synth : {e     : EXPR}
       -> {rs    : List Ty.Role}
       -> {ds,ls : List Ty.Base}
       -> {gs    : List Ty.Method }
       -> {ss    : List Ty.Session}
       -> (st    : State)
       -> (env   : Env rs ds ss gs ls)
       -> (syn   : Expr e)
                -> Capable (State, DPair Ty.Base (Expr rs ds ss gs ls))

  synth st env (Hole ref prf)
      = unknown (span ref)

  synth st env (Var ref prf)
      = do (ty ** idx) <- Lambda.lookup env ref
           pure (st, (ty ** Var idx))


  synth st env (LetTy fc ref k ty val scope)
    = do (st, (tyVal ** T tyTmVal val)) <- check st fc env ty val

         case k of
           HEAP
             => do (st, (tyS ** scope)) <- synth st (Lambda.extend env ref (REF tyVal)) scope

                   pure (st, (_ ** Let (TyRef tyTmVal) (Builtin Alloc [val]) scope))
           STACK
             => do (st, (tyS ** scope)) <- synth st (Lambda.extend env ref tyVal) scope

                   pure (st, (_ ** Let tyTmVal val scope))


  synth st env (Let fc ref k val scope)
    = do (st, (tyVal ** T tyTmVal val)) <- synthReflect st env val

         case k of
           HEAP
             => do (st, (tyS ** scope)) <- synth st (Lambda.extend env ref (REF tyVal)) scope

                   pure (st, (_ ** Let (TyRef tyTmVal) (Builtin Alloc [val]) scope))
           STACK
             => do (st, (tyS ** scope)) <- synth st (Lambda.extend env ref tyVal) scope

                   pure (st, (_ ** Let tyTmVal val scope))

  synth st env (Split fc this val scope)
    = do (st, (TUPLE (f::s::ts) ** v)) <- synth st env val
           | (st, (tyV ** _)) => throwAt fc (PairExpected tyV)

         envExt <- zip env this (f::s::ts)

         (st, (_ ** rest)) <- synth st envExt scope

         pure (st, (_ ** Split v rest))


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
  synth st env (Const fc UNIT v) = pure (st, (_ ** Builtin  U    Nil))
  synth st env (Const fc CHAR v) = pure (st, (_ ** Builtin (C v) Nil))
  synth st env (Const fc STR v)  = pure (st, (_ ** Builtin (S v) Nil))
  synth st env (Const fc INT v)  = pure (st, (_ ** Builtin (I v) Nil))
  synth st env (Const fc BOOL v) = pure (st, (_ ** Builtin (B v) Nil))

  -- [ NOTE ] @TODO The builtins could be factored out better.

  -- ### Boolean ops
  synth st env (OpBin fc AND l r)
    = do (st, res) <- checkBinOpB st env fc l r AND
         pure (st, (_ ** res))

  synth st env (OpBin fc OR  l r)
    = do (st, res) <- checkBinOpB st env fc l r OR
         pure (st, (_ ** res))

  synth st env (OpUn  fc NOT o)
    = do (st, T tyTm l) <- check st fc env TyBool o
         pure (st,  (_ ** Builtin Not [l]))

  -- ### Comparators
  synth st env (OpBin fc LT l r)
    = do (st, res) <- checkCmp st env fc l r LT
         pure (st, (_ ** res))

  synth st env (OpBin fc LTE l r)
     = do (st, res) <- checkCmp st env fc l r LTE
          pure (st, (_ ** res))

  synth st env (OpBin fc EQ l r)
    = do (st, res) <- checkCmp st env fc l r EQ
         pure (st, (_ ** res))

  synth st env (OpBin fc GT l r)
    = do (st, res) <- checkCmp st env fc l r GT
         pure (st, (_ ** res))

  synth st env (OpBin fc GTE l r)
    = do (st, res) <- checkCmp st env fc l r GTE
         pure (st, (_ ** res))

  -- ### Maths
  synth st env (OpBin fc ADD l r)
    = do (st, res) <- checkBinOpI st env fc l r ADD
         pure (st, (_ ** res))

  synth st env (OpBin fc SUB l r)
    = do (st, res) <- checkBinOpI st env fc l r SUB
         pure (st, (_ ** res))

  synth st env (OpBin fc MUL l r)
    = do (st, res) <- checkBinOpI st env fc l r MUL
         pure (st, (_ ** res))

  synth st env (OpBin fc DIV l r)
    = do (st, res) <- checkBinOpI st env fc l r DIV
         pure (st, (_ ** res))

  -- ### Strings & Chars
  synth st env (OpBin fc STRCONS h t)
    = do (st, T tyH h) <- check st fc env TyChar h
         (st, T tyT t) <- check st fc env TyStr  t
         pure (st, (_ ** Builtin (StrOp Cons) [h,t]))

  synth st env (OpUn fc SIZE o)
    = do (st, T tyTm t) <- check st fc env TyStr o
         pure (st, (_ ** Builtin (StrOp Length) [t]))

  synth st env (OpUn fc ORD o)
    = do (st, T tyTm t) <- check st fc env TyChar o
         pure (st, (_ ** Builtin (CharOp Ord) [t]))

  synth st env (OpUn fc CHR o)
    = do (st, T tyTm l) <- check st fc env TyInt o
         pure (st, (_ ** Builtin (CharOp Chr) [l]))

  synth st env (OpUn fc STRO o)
    = do (st, T tyTm l) <- check st fc env TyChar o
         pure (st, (_ ** Builtin (CharOp Singleton) [l]))

  synth st env (OpUn fc TOSTR l)
    = do (st, (ty ** l)) <- synth st env l

         maybe (throwAt fc Uncomparable)
               (\prf => pure (st, (_ ** Builtin (ToString prf) [l])))
               (cmpTy ty)

  -- ### Memory
  synth st env (OpBin fc MUT ptr val)
    = do (st, (tyV ** val)) <- synth st env val

         (st, (REF t ** ptr)) <- synth st env ptr
           | (st, (ty ** _)) => mismatchAt fc (REF tyV) (ty)

         Refl <- compare fc tyV t

         pure (st, (_ ** Builtin Mutate [ptr, val]))

  synth st env (OpUn fc FETCH ptr)
    = do (st, (REF t ** tm)) <- synth st env ptr
           | (st, (ty ** tm)) => throwAt fc (RefExpected ty)

         pure (st, (_ ** Builtin Fetch [tm]))

  -- ### Files
  synth st env (OpUn fc POPEN2 o)
    = do (st, T _ tm) <- check st fc env TyStr o

         pure (st, (_ ** Builtin POpen2 [tm]))

  synth st env (OpUn fc (OPEN k m) o)
    = do (st, T _ tm) <- check st fc env TyStr o

         pure (st, (_ ** Builtin (Open k m) [tm]))

  synth st env (OpBin fc WRITE h s)
    = do (st, (HANDLE k ** h)) <- synth st env h
           | (st, (ty ** _)) =>  throwAt fc (HandleExpected ty)

         (st, T _ s) <- check st fc env TyStr s

         pure (st, (_ ** Builtin WriteLn [h, s]))


  synth st env (OpUn fc READ o)
    = do (st, (HANDLE k ** h)) <- synth st env o
           | (st, (ty ** _)) =>  throwAt fc (HandleExpected ty)

         pure (st, (_ ** Builtin ReadLn [h]))

  synth st env (OpUn fc CLOSE o)
    = do (st, (HANDLE k ** h)) <- synth st env o
           | (st, (ty ** _)) => throwAt fc (HandleExpected ty)

         pure (st, (_ ** Builtin Close [h]))

  -- ### Side Effects
  synth st env (OpUn fc PRINT s)
    = do (st, T _ s) <- check st fc env TyStr s
         pure (st, (_ ** Builtin Print [s]))

  -- ## Lists

  synth st env (Length fc x)
    = do (st, (ty ** val)) <- synth st env x
         case ty of
           (LIST ty) => pure (st, (INT ** CountL val))
           (VECTOR type n) => pure (st, (INT ** CountV val))
           type => throwAt fc (IterableExpected type)

  synth st env (MkList fc Empty [])
    = unknown fc

  synth st env (MkList fc (Next Empty) (x :: []))
    = do (st, (ty ** x)) <- synth st env x
         pure (st, (_ ** MkList [x]))

  synth st env (MkList fc (Next (Next z)) (x :: (y :: w)))
    = do (st, (ty ** x)) <- synth st env x
         (st, (LIST ty' ** MkList xs)) <- synth st env (MkList fc (Next z) (y::w))
           | (st, (ty' ** _)) => mismatch (LIST ty) ty'

         Refl <- compare fc ty ty'

         pure (st, (_ ** MkList (x::xs)))


  synth st env (SetL fc idx tm val)
    = do (st, idx) <- check st fc env INT idx

         (st, (ty ** val)) <- synth st env val

         (st, tm) <- check st fc env (LIST ty) tm

         pure (st, (_ ** SetL idx tm val))

  synth st env (GetL fc idx tm)
    = do (st, idx) <- check st fc env INT idx

         (st, (LIST ty ** tm)) <- synth st env tm
           | (st, (ty ** _)) => throwAt fc (ListExpected ty)

         pure (st, (_ ** GetL idx tm))

  -- ## Vectors
  synth st env (MkVect fc Empty [])
    = unknown fc

  synth st env (MkVect fc (Next Empty) (x :: []))
    = do (st, (ty ** x)) <- synth st env x
         pure (st, (_ ** MkVect [x]))

  synth st env (MkVect fc (Next (Next z)) (x :: (y :: w)))
    = do (st, (ty ** x)) <- synth st env x
         (st, (VECTOR m ty' ** MkVect xs)) <- synth st env (MkVect fc (Next z) (y::w))
           | (st, (ty ** _)) => throwAt fc (VectorExpected ty)

         Refl <- compare fc ty m

         pure (st, (_ ** MkVect (x::xs)))

  synth st env (SetV fc idx tm val)
    = do (st, (ty ** val)) <- synth st env val

         (st, (VECTOR ty' m ** tm)) <- synth st env tm
           | (st, (ty ** _)) => throwAt fc (VectorExpected ty)

         Refl <- compare fc ty ty'

         ifThenElse (idx < 0)
                    (throwAt fc NatExpected)
                    (maybe (throwAt fc (OOB (cast idx) m))
                           (\idx => pure (st, (_ ** SetV idx tm val)))
                           (natToFin (cast idx) m))

  synth st env (GetV fc idx tm)
    = do (st, (VECTOR ty' m ** tm)) <- synth st env tm
           | (st, (ty ** _)) => throwAt fc (VectorExpected ty)

         ifThenElse (idx < 0)
                    (throwAt fc NatExpected)
                    (maybe (throwAt fc (OOB (cast idx) m))
                           (\idx => pure (st, (_ ** GetV idx tm)))
                           (natToFin (cast idx) m))

  synth st env (Slice fc st' ed tm)
    = do (st, T tyTm st') <- check st fc env (TyInt) st'
         (st, T tyTm ed) <- check st fc env (TyInt) ed
         (st, T tyTm tm) <- check st fc env (TyStr) tm
         pure (st, (_ ** Builtin (StrOp Slice) [st', ed, tm]))


  -- ## Pairs
  synth st env (MkTuple fc prf ts)
    = do (st, (_ ** (tyA::tyB::tys) ** (a::b::tms))) <- args st ts
           | _ => throwAt fc Unknown
         pure (st, (_ ** Tuple (a::b::tms)))

    where args : State -> {as' : _} -> Vect.Quantifiers.All.All Expr as'
              -> Capable (State, DPair Nat
                            (\n => DPair (Vect n Base)
                                         (DVect Base (Expr rs ds ss gs ls) n)))
          args st [] = pure (st, (_ ** _ ** Nil))

          args st (l :: y)
            = do (st, (ty ** tm)) <- synth st env l
                 (st, (n ** tys ** tms)) <- args st y
                 pure (st, (S n ** ty::tys ** tm::tms))

  synth st env (GetT fc loc tup)
    = do if loc < 0
          then throwAt fc (NatExpected)
          else do (st, (TUPLE ts ** tm)) <- synth st env tup
                    | (st, (ty ** _)) => throwAt fc (PairExpected ty)
                  maybe (throwAt fc (OOB (cast loc) (length ts)))
                        (\idx => pure (st, (_ ** GetT tm idx)))
                        (finFromVect (cast loc) ts)

  synth st env (SetT fc loc tup v)
    = do if loc < 0
           then throwAt fc (NatExpected)
           else do (st, (TUPLE ts ** tm)) <- synth st env tup
                      | (st, (ty ** _)) => throwAt fc (PairExpected ty)

                   maybe (throwAt fc (OOB (cast loc) (length ts)))
                         (\idx => do (st, (tyV ** tmV)) <- synth st env v
                                     Refl <- compare fc (index idx ts) tyV
                                     pure (st, (_ ** SetT tm idx tmV)))
                         (finFromVect (cast loc) ts)

  -- ## Records
  synth st env (Record fc prf (f::fs))
    = do (st, (_ ** f)) <- field st f

         (st, (_ ** fs)) <- fields st fs

         pure (st, (_ ** Record (f :: fs)))

    where field : State
               -> (giv : Field sco)
                      -> Capable (State, (DPair (String,Base) (Field rs ds ss gs ls)))
          field st (F fc s e)
            = do (st, (t ** tm)) <- synth st env e
                 pure (st, (_ ** F s tm))

          fields : State
                -> Vect.Quantifiers.All.All Field as'
                -> Capable (State, DPair (List (String, Base))
                              (DList (String,Base)
                                     (Field rs ds ss gs ls)))
          fields st Nil
            = pure (st, (_ ** Nil))

          fields st (f::fs)
            = do (st, (_ ** f)) <- field st f

                 (st, (_ ** fs)) <- fields st fs
                 pure (st, (_ ** f::fs))

  synth st env (GetR fc loc tup)
    = do (st, (RECORD (t:::ts) ** tm)) <- synth st env tup
            | (st, (ty ** _)) => throwAt fc (RecordExpected ty)

         (ty ** loc) <- isElem fc fc loc (t::ts)

         pure (st, (_ ** GetR tm loc))


  synth st env (SetR fc loc tup v)
    = do (st, (RECORD (t:::ts) ** tm)) <- synth st env tup
           | (st, (ty ** _)) => throwAt fc (RecordExpected ty)

         (ty ** loc) <- isElem fc fc loc (t::ts)

         (st, (tyV ** tmV)) <- synth st env v

         Refl <- compare fc ty tyV

         pure (st, (_ ** SetR tm loc tmV))


  -- ## Unions
  synth st env (Match fc cond prf (C fcC s sc c::cs))
    = do (st, (UNION ((s',cTy) ::: tys) ** cond)) <- synth st env cond
           | (st, (ty ** _)) => throwAt fc (UnionExpected ty)

         (st, (rTy ** cTm)) <- case' st fcC s' s sc cTy c

         (st, cTms) <- cases st fc rTy tys cs

         pure (st, (_ ** Match cond (cTm :: cTms)))

    where case' : {sco : _}
               -> State
               -> (fc  : FileContext)
               -> (s'  : String)
               -> (s   : String)
               -> (sc  : String)
               -> (cTy : Base)
               -> (giv : Expr sco)
                      -> Capable (State, DPair Base (\ret => Case rs ds ss gs ls ret (s',cTy)))
          case' st fc s' str sc cTy giv
            = do Refl <- embedAt fc (WrongLabel s' str) (decEq s' str)
                 (st, (rTy ** cTm)) <- synth st (Lambda.extend env sc cTy) giv
                 pure (st, (rTy ** C s' cTm))

          cases : State
               -> (fc : FileContext)
               -> (ret : Base)
               -> (exp : List (String, Base))
               -> Vect.Quantifiers.All.All Case as'
               -> Capable (State, DList (String,Base)
                             (Case rs ds ss gs ls ret)
                             exp)
          cases st _ ret Nil Nil
            = pure (st, Nil)

          cases _ fc ret Nil cs
            = throwAt fc (RedundantCases (flattern cs))

          cases _ fc ret es Nil
            = throwAt fc (CasesMissing es)

          cases st fc ret ((se,te)::exp) (C fcC sg sc c::cs)

            = do (st , (rTy' ** c')) <- case' st fcC se sg sc te c
                 Refl <- compare fcC ret rTy'

                 (st, rest) <- cases st fc ret exp cs
                 pure (st, c'::rest)


  synth _ env (Tag fc _ _)
    = unknown fc

  -- ## Ascriptions
  synth st env (The fc ty tm)
    = do (st, (_ ** T ty tm)) <- check st fc env ty tm
         pure (st, (_ ** tm))

  -- ## Control Flows
  synth st env (Cond fc c t f)
    = do (st, T _ c) <- check st fc env TyBool c

         (st, (tyT ** tt)) <- synth st env t

         (st, (tyF ** ff)) <- synth st env f

         Refl <- compare fc tyT tyF

         pure (st, (_ ** Cond c tt ff))

  synth st env (Seq fc this that)
    = do (st, T _ this) <- check st fc env TyUnit this
         (st, (ty ** that)) <- synth st env that

         pure (st, (_ ** Seq this that))

  synth st env (ForEach fc (MkRef fc s) R cond scope)
    = do (st, res) <- synth st env cond
         case res of
           (VECTOR ty sl ** c)
             => do (st, scope) <- check st fc (Lambda.extend env s ty) UNIT scope
                   pure (st, (_ ** ForEach c V scope))

           (LIST ty ** c)
             => do (st, scope) <- check st fc (Lambda.extend env s ty) UNIT scope
                   pure (st, (_ ** ForEach c L scope))

           (ty ** _) => throwAt fc (IterableExpected ty)

  synth st env (Loop fc scope cond)
    = do (st, (ty ** scope)) <- synth st env scope
         (st, T _ cond) <- check st fc env TyBool cond

         pure (st, (_ ** Loop scope cond))

  synth st env (Call fc (MkRef fc s) R prf argz)
    = do (FUNC argTys _ ** idx) <- Gamma.lookup env (MkRef fc s)
           | (ty ** _) => throwAt fc (FunctionExpected ty)
         (st,  args') <- args st fc argTys argz

         pure (st, (_ ** Call idx args'))

    where size : Vect.Quantifiers.All.All Expr as
              -> Nat
          size Nil = Z
          size (x::xs) = S (size xs)

          args : {as   : Vect n EXPR}
              -> State
              -> (fc   : FileContext)
              -> (tys  : List Ty.Base)
              -> (args : Vect.Quantifiers.All.All Expr as)
                      -> Capable (State, DList Ty.Base
                                    (Expr rs ds ss gs ls)
                                    tys)
          args st _ [] []
            = pure (st, Nil)

          args _ fc [] (elem :: rest)

            = throwAt fc (RedundantArgs (size (elem :: rest)))

          args _ fc (x :: xs) []
            = throwAt fc (ArgsExpected (x::xs))

          args st fc (x :: xs) (tm' :: tms)
            = do (st, (ty ** tm)) <- synth st env tm'

                 let Val (getFC q) = getFC tm'
                 Refl <- compare (getFC q) x ty

                 (st, rest) <- args st fc xs tms

                 pure (st, tm :: rest)

  synth st env (Run fc (MkRef fc s) R pA argz pV vs)
    = do (SESH ctxt whom prot argTys _ ** idx) <- Gamma.lookup env (MkRef fc s)
           | (ty ** _) => throwAt fc (SessionExpected ty)

         let (R pz proles) = hasRoles prot

         (st, args') <- args st fc argTys argz

         (st, asgns) <- assignments st ctxt pz vs
         pure (st, (_ ** Run idx
                        asgns
                        proles
                        args'))

    where size : Vect.Quantifiers.All.All Expr as
              -> Nat
          size Nil = Z
          size (x::xs) = S (size xs)

          args : {as   : Vect n EXPR}
              -> State
              -> (fc   : FileContext)
              -> (tys  : List Ty.Base)
              -> (args : Vect.Quantifiers.All.All Expr as)
                      -> Capable (State, DList Ty.Base
                                    (Expr rs ds ss gs ls)
                                    tys)
          args st _ [] []
            = pure (st, Nil)

          args _ fc [] (elem :: rest)

            = throwAt fc (RedundantArgs (size (elem :: rest)))

          args _ fc (x :: xs) []
            = throwAt fc (ArgsExpected (x::xs))

          args st fc (x :: xs) (tm' :: tms)
            = do (st, (ty ** tm)) <- synth st env tm'

                 let Val (getFC q) = getFC tm'
                 Refl <- compare (getFC q) x ty

                 (st, rest) <- args st fc xs tms

                 pure (st, tm :: rest)

          getNames : Vect.Quantifiers.All.All Val qs -> List String
          getNames Nil = Nil
          getNames (V fc (R s') _ :: rest) = s' :: getNames rest

          assignments : State
                     -> {vs   : Vect n (AST VAL)}
                     -> (ctxt : Context Role role)
                     -> (prs  : Roles role ps)
                     -> (vals : Vect.Quantifiers.All.All Val vs)
                     -> Capable (State, Assignments role rs ds ss gs ls p prs)
          assignments st _ [] []
            = pure (st, Empty)

          assignments _ _ [] (x :: y)
            = throwAt fc (RedundantRoles $ getNames (x::y))

          assignments _ renv (r :: rz) Nil
            = do let qq = mapToList (reflect renv) (r :: rz)
                 throwAt fc (RolesExpected qq)

          assignments st renv (r :: rz) (V fc' (R r') v::vs)
            = do let r'' = reflect renv r
                 Refl <- embedAt fc' (MismatchRole (MkRef fc' r') (MkRef fc' r''))
                                     (decEq r'' r')

                 (st, T _ tm) <- check st fc' env TyStr v
                 (st, rest) <- assignments st renv rz vs
                 pure (st, KV r tm rest)

  namespace View
    export
    check : {e        : EXPR}
         -> {rs       : List Ty.Role}
         -> {ds,ls : List Ty.Base} -> { gs : List Ty.Method }
         -> {ss       : List Ty.Session}
         -> State
         -> (fc       : FileContext)
         -> (env      : Env rs ds ss gs ls)
         -> (ty       : Ty t)
         -> (syn      : Expr e)
                     -> Capable (State, DPair Base (The rs ds ss gs ls))
    check st fc env ty syn
       = do (ty ** tm) <- synth (delta env) ty
            (st, res) <- check st fc env tm syn
            pure (st, (ty ** res))

  export
  check : {t        : Base}
       -> {e        : EXPR}
       -> {rs       : List Ty.Role}
       -> {ds,ls : List Ty.Base} -> { gs : List Ty.Method }
       -> {ss       : List Ty.Session}
       -> State
       -> (fc       : FileContext)
       -> (env      : Env rs ds ss gs ls)
       -> (ty       : Ty ds t)
       -> (syn      : Expr e)
                   -> Capable (State, The rs ds ss gs ls t)

  check {t = (LIST type)} st fc env tyTm (MkList fc' prf [])
    = pure (st, T tyTm (MkList Nil))

  check {t = (VECTOR type 0)} st fc env tyTm (MkVect fc' prf [])
    = pure (st, T tyTm (MkVect Nil))

  check {t = (VECTOR type (S k))} st fc env tyTm (MkVect fc' prf [])
    = mismatchAt fc (VECTOR type (S k)) (VECTOR type Z)

  check {t = (UNION (a:::as))} st fc env tyTm (Tag fc' s l)
    = do (ty ** loc) <- isElem fc fc' s (a::as)
         (st, (ty' ** tm)) <- synth st env l

         Refl <- compare fc' ty ty'
         pure (st, T tyTm (Tag s tm loc))

  check {t = t} st fc env ty (Hole (MkRef fc' s) R)
    = do let sta = addHole st s (HExpr fc' env s t)
         pure (sta, T ty $ Hole s)

    -- showHoleExit (lambda env) s t
         -- @TODO add infrastructure to collect all the holes, and then report.

  check {t = t} st fc env ty expr
    = do (st, (ty' ** e)) <- synth st env expr
         Refl <- compare fc t ty'
         pure (st, T ty e)

  namespace Reflect
    export
    synthReflect : {e        : EXPR}
                -> {rs       : List Ty.Role}
                -> {ds,ls : List Ty.Base}
                -> { gs : List Ty.Method }
                -> {ss       : List Ty.Session}
                -> State
                -> (env      : Env rs ds ss gs ls)
                -> (syn      : Expr e)
                            -> Capable (State, DPair Base (The rs ds ss gs ls))
    synthReflect st env syn
      = do (st, (ty ** expr)) <- Exprs.synth st env syn
           tm <- reflect (delta env) ty
           pure (st, (_ ** T tm expr))

    export
    check : {e        : EXPR}
         -> {rs       : List Ty.Role}
         -> {ds,ls : List Ty.Base}
         -> { gs : List Ty.Method }
         -> {ss       : List Ty.Session}
         -> State
         -> (fc       : FileContext)
         -> (env      : Env rs ds ss gs ls)
         -> (ty       : Base)
         -> (syn      : Expr e)
                     -> Capable (State, Expr rs ds ss gs ls ty)
    check st fc env ty syn
      = do tm <- reflect (delta env) ty
           (st, T _ tm) <- check st fc env tm syn
           pure (st, tm)


namespace Raw
  export
  synth : {rs       : List Ty.Role}
       -> {ds,ls : List Ty.Base} -> { gs : List Ty.Method }
       -> {ss       : List Ty.Session}
       -> State
       -> (env      : Env rs ds ss gs ls)
       -> (syn      : EXPR)
                   -> Capable (State, DPair Ty.Base (Expr rs ds ss gs ls))
  synth st env e
    = synth st env (toExpr e)

-- [ EOF ]
