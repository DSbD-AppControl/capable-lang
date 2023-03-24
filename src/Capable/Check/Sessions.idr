||| Type-checker for sessions.
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Capable.Check.Sessions

import Toolkit.Data.Location

import Capable.Types
import Capable.Types.Protocol.Projection
import Capable.Types.Protocol.Selection
import Capable.Core

import Capable.Raw.AST
import Capable.Raw.Role
import Capable.Raw.Types
import Capable.Raw.Exprs
import Capable.Raw.Funcs
import Capable.Raw.Protocols
import Capable.Raw.Sessions


import Capable.Check.Common

import Capable.Check.Roles
import Capable.Check.Types
import Capable.Check.Exprs
import Capable.Check.Funcs
import Capable.Check.Protocols

import Capable.Terms.Vars
import Capable.Terms.Roles
import Capable.Terms.Types
import Capable.Terms.Exprs
import Capable.Terms.Protocols

import Capable.Terms.Sessions
import Capable.Terms.Funcs

%default total


{-
  public export
  data Offer : (s : AST OFFER) -> Type where
    O : (fc : FileContext)
     -> (t,s  : String)
     -> (c    : Expr sc)
             -> Offer (Branch (OFFER t s) fc [sc])

  public export
  data Expr : (s : Raw.AST.EXPRSESH) -> Type
-}


check : {e, ls : _}
     -> {rs   : List Ty.Role}
     -> {ds   : List Ty.Base}
     -> {gs   : List Ty.Method}
     -> {ss   : List Ty.Session}
     -> (env  : Env rs ds ss gs ls)
     -> (enr  : Context Role roles)
     -> (enc  : Context Protocol.Kind ks)
     -> (princ : Role roles)
     -> (ret  : Base)
     -> (type : Local ks roles)
     -> (expr : Sessions.Expr e)
             -> Capable (Expr roles rs ds ss gs ls ks princ type ret)

check env er _ princ ret Crash (Crash fc expr)
  = do tm <- check fc env ret expr
       pure (Crash tm)

check env er _ princ ret End (End fc expr)
  = do tm <- check fc env ret expr
       pure (End tm)

check env er ec princ ret (Call x) (Call fc a)
  = do (R ** idx) <- lookup ec (MkRef fc a) -- @TODO change to ref

       case Index.decEq x idx of
         Yes (Same Refl Refl) => pure (Call idx)
         No co => throwAt fc (MismatchK (reflect ec x) a)

check env er ec princ ret (Rec x) (LetRec fc s expr)
  = do tm <- check env er (I s R :: ec) princ ret x expr
       pure (LetRec tm)

check env er ec princ ret (Choice BRANCH whom (Val (UNION (b:::bs))) prfM (c::cs)) (Read fc r prf offs onEr)
    = do (MkRole ** target) <- synth er r

         (Same Refl Refl) <- embedAt fc
                                     (MismatchRoleS (let R s = r in s ) -- otherwise fc is inaccessible...
                                                    (reflect er whom))
                                     (Index.decEq whom target)

         offs <- offers fc (c::cs) offs
         err  <- check env er ec princ ret (Crash) onEr

         pure (Read target prfM offs err)

    where offer : (fc  : FileContext)
               -> (b   : Branch Local ks roles (s,t))
               -> (o   : Offer oraw)
                      -> Capable (Offer roles rs ds ss gs ls ks ret princ b)
          offer fc (B l mtype ctype) (O fc' l' mname cont)
            = do Refl <- embedAt fc' (WrongLabel l l') (decEq l l')
                 cont <- check (Lambda.extend env mname mtype) er ec princ ret ctype cont
                 pure (O l cont)

          flatBranches : Local.Branches ks roles lts -> List (String, Base)
          flatBranches = mapToList (\(B s l c) => (s,l))

          offers : (fc : FileContext)
                -> (bs : Local.Branches ks roles lts)
                -> (os : Vect.Quantifiers.All.All Offer as')
                      -> Capable (Offers roles rs ds ss gs ls ks ret princ bs)
          offers fc Nil Nil
            = pure Nil

          offers fc Nil os
            = throwAt fc (RedundantCases (flattern os))

          offers fc bs Nil
            = throwAt fc (CasesMissing (flatBranches bs))

          offers fc (B l t c::bs) (o::os)
            = do o' <- offer fc (B l t c) o
                 rest <- offers fc bs os
                 pure (o'::rest)


check env er ec princ ret (Choice SELECT whom (Val (UNION (f:::fs))) (UNION (p::ps)) (c::cs)) (Send fc r l msg body onEr)
  = do (MkRole ** target) <- synth er r

       (Same Refl Refl) <- embedAt fc
                                   (MismatchRoleS (let R s = r in s ) -- otherwise fc is inaccessible...
                                                  (reflect er whom))
                                   (Index.decEq whom target)

       R tyM cont prf sel <- embedAt fc (LabelMismatch l (map fst $ f::fs))
                                        (select l (p::ps) (c::cs))

       (tyM' ** tmM) <- synth env msg

       Refl <- compare fc tyM tyM'

       rest <- check env er ec princ ret cont body

       err <- check env er ec princ ret (Crash) onEr

       pure (Send target tmM prf sel rest err)

check env er ec princ ret type (Seq fc x y)
  = do tmL <- check fc env UNIT x
       tmR <- check env er ec princ ret type y
       pure (Seq tmL tmR)

check env er ec princ ret type (LetTy fc ref st ty val scope)
    = do (tyVal ** T tyTmVal val) <- check fc env ty val

         case st of
           HEAP
             => do scope <- check (Lambda.extend env ref (REF tyVal))
                                   er
                                   ec
                                   princ
                                   ret
                                   type
                                   scope

                   pure (Let (TyRef tyTmVal) (Builtin Alloc [val]) scope)
           STACK
             => do scope <- check (Lambda.extend env ref tyVal)
                                   er
                                   ec
                                   princ
                                   ret
                                   type
                                   scope

                   pure (Let tyTmVal val scope)

check env er ec princ ret type (Let fc ref st val scope)
    = do (tyVal ** T tyTmVal val) <- synthReflect env val

         case st of
           HEAP
             => do scope <- check (Lambda.extend env ref (REF tyVal))
                                           er
                                           ec
                                           princ
                                           ret
                                           type
                                           scope

                   pure (Let (TyRef tyTmVal) (Builtin Alloc [val]) scope)
           STACK
             => do scope <- check (Lambda.extend env ref tyVal)
                                           er
                                           ec
                                           princ
                                           ret
                                           type
                                           scope

                   pure (Let tyTmVal val scope)

check env er ec princ ret type (Split fc this val scope)
    = do (TUPLE (f::s::ts) ** v) <- synth env val
           | (tyV ** _) => throwAt fc (PairExpected tyV)

         envExt <- zip env this (f::s::ts)

         rest <- check envExt er ec princ ret type scope

         pure (Split v rest)

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

check env er ec princ ret type (Hole ref prf)
  = showHoleSessionExit (lambda env)
                        er
                        ec
                        type
                        (get ref)

check env er _ princ ret Crash expr
  = let fc = getFC expr in throwAt fc (IllTypedSession "Crash Expected")

check env er _ princ ret End expr
  = throwAt (getFC expr) (IllTypedSession "End expected")

check env er _ princ ret (Call x) expr
  = throwAt (getFC expr) (IllTypedSession "Recursive call expected")

check env er _ princ ret (Rec x) expr
  = throwAt (getFC expr) (IllTypedSession "Recursive var to be introduced")

check env er _ princ ret (Choice SELECT whom type prfM choices) expr
  = throwAt (getFC expr) (IllTypedSession "A send needs to be made")

check env er _ princ ret (Choice BRANCH whom type prfM choices) expr
  = throwAt (getFC expr) (IllTypedSession "An offer needs to be made")

export
synth : {rs   : List Ty.Role}
     -> {ds   : List Ty.Base}
     -> {gs   : List Ty.Method}
     -> {ss   : List Ty.Session}
     -> (env  : Env rs ds ss gs Nil)
     -> (sesh : Session s)
             -> Capable (DPair Ty.Method (Session rs ds ss gs))
synth env (Sesh fc prin ref p prf as ret scope)
  = do (S rh tyGlobal ** prot) <- Sigma.lookup env ref

       (MkRole ** principle) <- synth rh prin

       (tyARGS ** as) <- args (delta env) as

       (tyRET ** ret) <- synth (delta env) ret

       (tyLocal ** tm) <- embedAt fc
                                  (ProjectionError) -- @TODO Error messages.
                                  (Projection.Closed.project principle tyGlobal)

       tm <- check ({ lambda := expand as} env) rh Nil principle tyRET tyLocal scope
       pure (SESH rh principle tyLocal tyARGS tyRET ** Sesh tm)

namespace Raw
  export
  synth : {rs  : List Ty.Role}
       -> {ds  : List Ty.Base}
       -> {gs  : List Ty.Method}
       -> {ss  : List Ty.Session}
       -> (env : Env rs ds ss gs Nil)
       -> (syn : AST SESH)
              -> Capable (DPair Ty.Method (Session rs ds ss gs))
  synth env s
    = synth env (toSession s)
-- [ EOF ]
