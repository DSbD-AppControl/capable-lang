||| Type-checker for sessions.
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Capable.Check.Sessions

import Data.String
import Toolkit.Data.Location

import Capable.Types
import Capable.Types.Protocol.Projection
import Capable.Types.Protocol.Selection
import Capable.Types.Protocol.Unification
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

namespace Expr
  namespace Check
    public export
    data Result : (roles, rs : List Ty.Role)
               -> (ds   : List Ty.Base)
               -> (ss   : List Ty.Session)
               -> (gs   : List Ty.Method)
               -> (ks   : List Protocol.Kind)
               -> (ls   : List Ty.Base)
               -> (p    : DeBruijn.Role roles p')
               -> (l    : Local.Local ks roles)
               -> (ret  : Base)
                       -> Type
      where
        R : (syn  : Synth.Local ks roles)
         -> (prf  : Unify chk syn)
         -> (expr : Expr   roles rs ds ss gs ls ks p syn ret)
                 -> Result roles rs ds ss gs ks ls p chk ret


    namespace Case
      public export
      data Result : (roles, rs : List Ty.Role)
                 -> (ds   : List Ty.Base)
                 -> (ss   : List Ty.Session)
                 -> (gs   : List Ty.Method)
                 -> (ks   : List Protocol.Kind)
                 -> (ls   : List Ty.Base)
                 -> (p    : DeBruijn.Role roles p')
                 -> (lt   : Pair String Base)
                 -> (b    : Local.Local ks roles)
                 -> (ret  : Base)
                         -> Type
        where
          C : {cchk : Local.Local ks roles}
           -> (csyn : Synth.Local ks roles)
           -> (prf  : Unify cchk
                            csyn)
           -> (expr : Case roles rs ds ss gs ls ks ret p (l,t) (B l t csyn))
                  -> Result roles rs ds ss gs ks ls p (l,t) cchk ret

    namespace Offer
      public export
      data Result : (roles, rs : List Ty.Role)
                 -> (ds   : List Ty.Base)
                 -> (ss   : List Ty.Session)
                 -> (gs   : List Ty.Method)
                 -> (ks   : List Protocol.Kind)
                 -> (ls   : List Ty.Base)
                 -> (p    : DeBruijn.Role roles p')
                 -> (b    : Branch Local.Local ks roles (l,t))
                 -> (ret  : Base)
                         -> Type
        where
          O : (csyn : Synth.Local ks roles)
           -> (prf  : Unify (B l t cchk)
                            (B l t csyn))
           -> (expr : Offer roles rs ds ss gs ls ks ret p (B l t csyn))
                  -> Result roles rs ds ss gs ks ls p (B l t cchk) ret

    namespace Cases
      public export
      data Result : (roles, rs : List Ty.Role)
                 -> (ds   : List Ty.Base)
                 -> (ss   : List Ty.Session)
                 -> (gs   : List Ty.Method)
                 -> (ks   : List Protocol.Kind)
                 -> (ls   : List Ty.Base)
                 -> (p    : DeBruijn.Role roles p')
                 -> (lts  : List (Pair String Base))
                 -> (bs   : Local.Local ks roles)
                 -> (ret  : Base)
                         -> Type
        where
          CS : {chk  : Local.Local ks roles}
            -> (syn  : Synth.Branches ks roles lts)
            -> (prf  : Cases.Unify chk syn)
            -> (expr : Cases roles rs ds ss gs ls ks ret p lts syn)
                    -> Result roles rs ds ss gs ks ls p lts chk ret

    namespace Offers
      public export
      data Result : (roles, rs : List Ty.Role)
                 -> (ds   : List Ty.Base)
                 -> (ss   : List Ty.Session)
                 -> (gs   : List Ty.Method)
                 -> (ks   : List Protocol.Kind)
                 -> (ls   : List Ty.Base)
                 -> (p    : DeBruijn.Role roles p')
                 -> (bs   : Local.Branches ks roles lts)
                 -> (ret  : Base)
                         -> Type
        where
          OS : {chk  : Local.Branches ks roles lts}
            -> (syn  : Synth.Branches ks roles lts)
            -> (prf  : Unify chk syn)
            -> (expr : Offers roles rs ds ss gs ls ks ret p syn)
                    -> Result roles rs ds ss gs ks ls p chk ret

  namespace Synth
    public export
    data Result : (roles, rs : List Ty.Role)
               -> (ds   : List Ty.Base)
               -> (ss   : List Ty.Session)
               -> (gs   : List Ty.Method)
               -> (ks   : List Protocol.Kind)
               -> (ls   : List Ty.Base)
               -> (p    : DeBruijn.Role roles p')
               -> (ret  : Base)
                       -> Type
      where
        R : (l    : Synth.Local ks roles)
         -> (expr : Expr   roles rs ds ss gs ls ks p l ret)
                 -> Result roles rs ds ss gs ks ls p ret

    namespace Case
      public export
      data Result : (roles, rs : List Ty.Role)
                 -> (ds   : List Ty.Base)
                 -> (ss   : List Ty.Session)
                 -> (gs   : List Ty.Method)
                 -> (ks   : List Protocol.Kind)
                 -> (ls   : List Ty.Base)
                 -> (p    : DeBruijn.Role roles p')
                 -> (s    : (String,Base))
                 -> (ret  : Base)
                         -> Type
        where
          C : (b    : Branch Synth.Local ks roles (s,t))
           -> (expr : Case roles rs ds ss gs ls ks ret p (s,t) b)
                  -> Result roles rs ds ss gs ks ls p (s,t) ret

    namespace Cases
      public export
      data Result : (roles, rs : List Ty.Role)
                 -> (ds   : List Ty.Base)
                 -> (ss   : List Ty.Session)
                 -> (gs   : List Ty.Method)
                 -> (ks   : List Protocol.Kind)
                 -> (ls   : List Ty.Base)
                 -> (p    : DeBruijn.Role roles p')
                 -> (lts  : List (String,Base))
                 -> (ret  : Base)
                         -> Type
        where
          CS : {lts : _}
           -> (bs   : Synth.Branches ks roles lts)
           -> (expr : Cases roles rs ds ss gs ls ks ret p lts bs)
                   -> Result roles rs ds ss gs ks ls p lts ret
    namespace Offer
      public export
      data Result : (roles, rs : List Ty.Role)
                 -> (ds   : List Ty.Base)
                 -> (ss   : List Ty.Session)
                 -> (gs   : List Ty.Method)
                 -> (ks   : List Protocol.Kind)
                 -> (ls   : List Ty.Base)
                 -> (p    : DeBruijn.Role roles p')
                 -> (s    : (String,Base))
                 -> (ret  : Base)
                         -> Type
        where
          O : (b    : Branch Synth.Local ks roles (s,t))
           -> (expr : Offer roles rs ds ss gs ls ks ret p b)
                  -> Result roles rs ds ss gs ks ls p (s,t) ret

    namespace Offers
      public export
      data Result : (roles, rs : List Ty.Role)
                 -> (ds   : List Ty.Base)
                 -> (ss   : List Ty.Session)
                 -> (gs   : List Ty.Method)
                 -> (ks   : List Protocol.Kind)
                 -> (ls   : List Ty.Base)
                 -> (p    : DeBruijn.Role roles p')
                 -> (lts  : List (String,Base))
                 -> (ret  : Base)
                         -> Type
        where
          OS : {lts : _}
           -> (bs   : Synth.Branches ks roles lts)
           -> (expr : Offers roles rs ds ss gs ls ks ret p bs)
                   -> Result roles rs ds ss gs ks ls p lts ret

  namespace Exprs

    synth : {e, roles, ls, ks : _}
         -> {rs    : List Ty.Role}
         -> {ds    : List Ty.Base}
         -> {gs    : List Ty.Method}
         -> {ss    : List Ty.Session}
         -> (env   : Env rs ds ss gs ls)
         -> (enr   : Context Role roles)
         -> (enc   : Context Protocol.Kind ks)
         -> (princ : DeBruijn.Role roles p')
         -> (ret   : Base)
         -> (expr  : Sessions.Expr e)
                  -> Capable (Synth.Result roles rs ds ss gs ks ls princ ret)

    -- [ NOTE ] Session Typed Terms

    synth env er ec p ret (Hole ref prf)
      = unknown (span ref)

    synth env er ec p ret (Call fc ref)
      = do (r ** idx) <- lookup ec (MkRef fc ref)
           -- @TODO change to ref

           pure (R (Call idx) (Call idx))

    synth env er ec p ret (Crash fc expr)
      = do tm <- check fc env ret expr
           pure (R Crash (Crash tm))

    synth env er ec p ret (End fc expr)

      = do tm <- check fc env ret expr
           pure (R End (End tm))

    synth env er ec p ret (Cond fc cond tt ff)
      = do tm <- check fc env BOOL cond
           R tyT tmT <- synth env er ec p ret tt
           R tyF tmF <- synth env er ec p ret ff

           pure (R (Choices [B "true" UNIT tyT, B "false" UNIT tyF]) (Cond tm tmT tmF))

    synth env er ec p ret (Match fc cond prf (c::cs))
      = do (UNION ((es,et) ::: fs) ** tm) <- synth env cond
               | (ty ** _) => throwAt fc (UnionExpected ty)

           C  b  a  <- case' fc ret es et c
           CS bs as <- cases fc ret  fs   cs

           pure (R (Choices (b::bs))
                   (Match tm (a::as))
                         -- (Match tm (a::as))
                   )

      where case' : (fc   : FileContext)
                 -> (ret  : Base)
                 -> (expL : String)
                 -> (et   : Base)
                 -> (o    : Offer oraw)
                         -> Capable (Case.Result roles rs ds ss gs ks ls p (expL,et) ret)
            case' fc ret el et (O fc' l' mn cont)
              = do Refl <- embedAt fc' (WrongLabel el l')
                                       (decEq el l')
                   R local cont <- synth (Lambda.extend env mn et)
                                                 er ec p ret cont
                   pure (C (B el et local) (C el cont))

            cases : (fc : FileContext)
                 -> (ret : Base)
                 -> (bs : List (String,Base))
                 -> (os : Vect.Quantifiers.All.All Offer as')
                       -> Capable (Cases.Result roles rs ds ss gs ks ls p bs ret)
            cases fc _ Nil Nil
              = pure (CS Nil Nil)

            cases fc _ Nil os
              = throwAt fc (RedundantCases (flattern os))

            cases fc _ bs Nil
              = throwAt fc (CasesMissing bs)

            cases fc ret ((expL,expTy)::bs) (o::os)
              = do C (B l t b) o' <- case' fc ret expL expTy o
                   CS bs os <- cases fc ret bs os

                   pure (CS (B l t b::bs) ((::) o' os))


    synth env er ec p ret (LetRec fc s scope)
      = do (R l tm) <- synth env er (I s (R s) :: ec) p ret scope
           pure (R (Rec _ l) (LetRec tm))


    synth env er ec p ret (Read fc r ty prf (ofs::offs) onEr)
        = do (UNION ((es,et) ::: fs) ** _) <- synth (delta env) ty
               | (ty ** _) => throwAt fc (UnionExpected ty)

             prfM <- embedAt fc (\prf => NotMarshable (UNION ((es,et):::fs)) prf)
                                (marshable (UNION ((es,et):::fs)))

             (r' ** target) <- synth er r

             O  b  o    <- offer  fc ret es et ofs
             OS bs offs <- offers fc ret   fs  offs

             R Crash err  <- synth env er ec p ret onEr
                | R type _ => throwAt fc (IllTypedSession "\{toString ec er type}")

             pure (R (Offer target
                            (Val (UNION ((es,et) ::: fs)))
                            prfM
                            (b::bs)
                                           )
                     (Read target prfM (o::offs) err))

        where offer : (fc   : FileContext)
                   -> (ret  : Base)
                   -> (expL : String)
                   -> (et   : Base)
                   -> (o    : Offer oraw)
                           -> Capable (Offer.Result roles rs ds ss gs ks ls p (expL,et) ret)
              offer fc ret expL expTy (O fc' l' mname cont)
                = do Refl <- embedAt fc' (WrongLabel expL l')
                                         (decEq expL l')
                     R local cont <- synth (Lambda.extend env mname expTy)
                                                 er ec p ret cont
                     pure (O (B expL expTy local) (O expL cont))


              offers : (fc : FileContext)
                    -> (ret : Base)
                    -> (bs : List (String,Base))
                    -> (os : Vect.Quantifiers.All.All Offer as')
                          -> Capable (Synth.Offers.Result roles rs ds ss gs ks ls p bs ret)
              offers fc _ Nil Nil
                = pure (OS Nil Nil)

              offers fc _ Nil os
                = throwAt fc (RedundantCases (flattern os))

              offers fc _ bs Nil
                = throwAt fc (CasesMissing bs)

              offers fc ret ((expL,expTy)::bs) (o::os)
                = do O (B l t b) o' <- offer fc ret expL expTy o
                     OS bs os <- offers fc ret bs os

                     pure (OS (B l t b::bs) ((::) o' os))


    synth env er ec p ret (Send fc role tyTm label msg scope onErr)
      = do -- 1. Check the type of the annotation

           (UNION ((es,et) ::: fs) ** cond) <- synth (delta env) tyTm
             | (ty ** _) => throwAt fc (UnionExpected ty)

           -- 2. Get the role.
           (r ** target) <- synth er role

           -- 3. Get the type of the payload.
           (tyM' ** tmM) <- synth env msg

           -- 4. Check if marshable
           prfM <- embedAt fc (NotMarshable tyM')
                              (marshable tyM')

           -- 5. Check is value tag.
           (ty ** loc) <- isElem fc fc label ((es,et)::fs)

           (R lsytn rest) <- synth env er ec p ret scope

           R Crash err  <- synth env er ec p ret onErr
              | R type _ => throwAt fc (IllTypedSession "TODO")

           pure (R (Select target
                           label
                           tyM'
                           prfM
                           lsytn)
                   (Send target label tmM prfM rest err))

    -- [ NOTE ] Non-Session-Typed Terms

    synth env er ec p ret (Seq fc x y)
      = do tmL <- check fc env UNIT x
           R l tmR <- synth env er ec p ret y
           pure (R l (Seq tmL tmR))

    synth env er ec p ret (LetTy fc ref st ty val scope)
      = do (tyVal ** T tyTmVal val) <- check fc env ty val

           case st of
             HEAP
               => do (R l scope) <- synth (Lambda.extend env ref (REF tyVal))
                                              er
                                              ec
                                              p
                                              ret
                                              scope

                     pure (R _ (Let (TyRef tyTmVal) (Builtin Alloc [val]) scope))
             STACK
               => do (R l scope) <- synth (Lambda.extend env ref tyVal)
                                              er
                                              ec
                                              p
                                              ret
                                              scope

                     pure (R _ (Let tyTmVal val scope))

    synth env er ec p ret (Let fc ref st val scope)
        = do (tyVal ** T tyTmVal val) <- synthReflect env val

             case st of
               HEAP
                 => do (R l scope) <- synth (Lambda.extend env ref (REF tyVal))
                                                 er
                                                 ec
                                                 p
                                                 ret
                                                 scope

                       pure (R l (Let (TyRef tyTmVal) (Builtin Alloc [val]) scope))
               STACK
                 => do (R l scope) <- synth (Lambda.extend env ref tyVal)
                                               er
                                               ec
                                               p
                                               ret
                                               scope

                       pure (R l (Let tyTmVal val scope))

    synth env er ec p ret (Split fc this val scope)
        = do (TUPLE (f::s::ts) ** v) <- synth env val
               | (tyV ** _) => throwAt fc (PairExpected tyV)

             envExt <- zip env this (f::s::ts)

             (R l rest) <- synth envExt er ec p ret scope

             pure (R l (Split v rest))

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


    partial export
    check : {e, roles, ls,ks : _}
         -> {rs   : List Ty.Role}
         -> {ds   : List Ty.Base}
         -> {gs   : List Ty.Method}
         -> {ss   : List Ty.Session}
         -> (env  : Env rs ds ss gs ls)
         -> (enr  : Context Role roles)
         -> (enc  : Context Protocol.Kind ks)
         -> (princ : DeBruijn.Role roles p)
         -> (ret  : Base)
         -> (type : Local.Local ks roles)
         -> (expr : Sessions.Expr e)
                 -> Capable (Check.Result roles rs ds ss gs ks ls princ type ret)


    -- [ NOTE ] Session Typed Terms

    --
    check e er ec p ret End (End fc expr)
      = do tm <- check fc e ret expr
           pure (R End End (End tm))

    --
    check e er ec p ret Crash (Crash fc expr)
      = do tm <- check fc e ret expr
           pure (R Crash Crash (Crash tm))

    --
    check e er ec princ ret (Call x) (Call fc ref)
      = do (r ** idx) <- lookup ec (MkRef fc ref)
           -- @TODO change to ref

           Same Refl Refl <- embedAt fc
                                     (MismatchK (reflect ec x) ref)
                                     (Index.decEq x idx)

           pure (R (Call idx) Call (Call idx))


    --
    check e er ec p ret (Rec l type) (LetRec fc s scope)
      = do R lsyn prf tm <- check e
                                  er
                                  (I s l :: ec)
                                  p
                                  ret
                                  type
                                  scope

           pure (R (Rec _ lsyn) (Rec prf) (LetRec tm))


    --
    check e er ec p ret (Choice BRANCH whom (Val (UNION ((l,t):::fs)))
                                                 (UNION (m::ms))
                                                        (B l t c::cs))
                        (Read fc role tyTm _ (o::os) onErr)

      = do -- 1. Check the type of the annotation

           (UNION ((lf,tf) ::: fields) ** tyTm) <- synth (delta e) tyTm
             | (ty ** _) => throwAt fc (UnionExpected ty)

           Refl <- compare fc (UNION ((lf,tf) ::: fields))
                              (UNION ((l, t)  ::: fs))

           prfM <- embedAt fc (\prf => NotMarshable (UNION ((lf,tf):::fields)) prf)
                              (marshable (UNION ((lf,tf):::fields)))


           -- 2. Check that the role is correct
           (r ** target) <- synth er role

           Same Refl Refl <- embedAt fc
                                     (MismatchRoleS (let R s = role in s)
                                                    (reflect er whom))
                                     (Index.decEq whom target)

           -- 3. Check the branches
           O  synO  prfO  o  <- offer  fc ret (B lf tf c) o
           OS synOS prfOS os <- offers fc ret          cs os

           -- 4. check the error branch
           R Crash Crash onErr <- check e er ec p ret Crash onErr

           -- 5. Return Evidence
           pure (R
                   (Offer target (Val (UNION ((lf,tf):::fields)))
                                 (UNION (m::ms))
                                 (B lf tf synO::synOS))
                   (Choice (prfO::prfOS))
                   (Read target
                         (UNION (m::ms))
                         (o::os)
                         onErr)
                   )

        where offer : (fc  : FileContext)
                   -> (ret : Base)
                   -> (b   : Branch Local.Local ks roles (lg,tg))
                   -> (o   : Offer oraw)
                          -> Capable (Check.Offer.Result roles rs ds ss gs ks ls p b ret)
              offer fc ret (B lg tg tyC) (O fc' l' m cont)
                = do Refl <- embedAt fc' (WrongLabel lg l')
                                         (decEq lg l')

                     R tySyn pU tm <- check (Lambda.extend e m tg)
                                            er
                                            ec
                                            p
                                            ret
                                            tyC
                                            cont
                     pure (O tySyn
                             (B pU) -- (B pU)
                             (O l' tm) -- (O l tm)
                             )

              offers : (fc  : FileContext)
                    -> (ret : Base)
                    -> (bs  : Local.Branches ks roles bs')
                    -> (os  : Vect.Quantifiers.All.All Offer as')
                           -> Capable (Check.Offers.Result roles rs ds ss gs ks ls p bs ret)

              offers fc _ Nil Nil
                = pure (OS Nil Nil Offers.Nil)

              offers fc _ Nil os
                = throwAt fc (RedundantCases (flattern os))

              offers fc _ bs Nil
                = do let Val bs = getLTs bs
                     throwAt fc (CasesMissing bs)

              offers fc ret ((B l t b)::bs) (o::os)
                = do O  lSyn  pU  o  <- offer  fc ret (B l t b) o
                     OS lSyns pUs os <- offers fc ret bs os
                     pure (OS (B l t lSyn::lSyns)
                              (pU::pUs)
                              (o::os))

    --
    check e er ec p ret (Choice SELECT whom (Val (UNION (f:::fs)))
                                                 (UNION (m::ms))
                                                        (c::cs))
                        (Send fc role tyTm label msg scope onErr)

      = do -- 1. Check the type of the annotation

           (UNION (field ::: fields) ** tyTm) <- synth (delta e) tyTm
             | (ty ** _) => throwAt fc (UnionExpected ty)

           Refl <- compare fc (UNION (field ::: fields))
                              (UNION (f     ::: fs))

           -- 2. Check that the role is correct
           (r ** target) <- synth er role

           Same Refl Refl <- embedAt fc
                                     (MismatchRoleS (let R s = role in s)
                                                    (reflect er whom))
                                     (Index.decEq whom target)

           -- 3. Is it a valid payload i.e. tagged union
           R tyM tyC (F label prfM) sel <- embedAt fc (LabelMismatch label
                                                                  (map fst $ f::fs))
                                                      (select label (m::ms) (c::cs))

           tmM <- check fc e tyM msg

           -- 4. Check the remainder of the protocol
           R tySyn pU scope <- check e er ec p ret tyC scope

           R Crash Crash onErr <- check e er ec p ret Crash onErr

           -- 5. Return Evidence

           pure (R (Select target label tyM prfM tySyn)
                   (Select sel pU)
                   (Send target label tmM prfM scope onErr))

    -- [ NOTE ] Non-Session Typed Terms

    check e er ec p ret type (Seq fc x y)

      = do tmL <- check fc e UNIT x
           R lSyn pU tmR <- check e er ec p ret type y
           pure (R lSyn pU (Seq tmL tmR))

    --
    check e er ec p ret type (LetTy fc ref st ty val scope)
      = do (tyVal ** T tyTmVal val) <- check fc e ty val

           case st of
             HEAP
               => do (R lSyn pU scope) <- check (Lambda.extend e ref (REF tyVal))
                                              er
                                              ec
                                              p
                                              ret
                                              type
                                              scope

                     pure (R lSyn pU (Let (TyRef tyTmVal) (Builtin Alloc [val]) scope))
             STACK
               => do (R lSyn pU scope) <- check (Lambda.extend e ref tyVal)
                                              er
                                              ec
                                              p
                                              ret
                                              type
                                              scope

                     pure (R lSyn pU (Let tyTmVal val scope))

    check e er ec p ret type (Let fc ref st val scope)
      = do (tyVal ** T tyTmVal val) <- synthReflect e val

           case st of
             HEAP
               => do (R l pU scope) <- check (Lambda.extend e ref (REF tyVal))
                                               er
                                               ec
                                               p
                                               ret
                                               type
                                               scope

                     pure (R l pU (Let (TyRef tyTmVal) (Builtin Alloc [val]) scope))
             STACK
               => do (R l pU scope) <- check (Lambda.extend e ref tyVal)
                                             er
                                             ec
                                             p
                                             ret
                                             type
                                             scope

                     pure (R l pU (Let tyTmVal val scope))

    check e er ec p ret type (Split fc this val scope)

      = do (TUPLE (f::s::ts) ** v) <- synth e val
             | (tyV ** _) => throwAt fc (PairExpected tyV)

           envExt <- zip e this (f::s::ts)

           (R l p rest) <- check envExt er ec p ret type scope

           pure (R l p (Split v rest))

      where zip : (env : Env rs ds ss gs ls)
               -> (xs  : List String)
               -> (ys  : Vect m Base)
                      -> Capable (Env rs ds ss gs
                                      (Extra.toList ys ++ ls))
            zip env [] [] = pure env
            zip env [] (x :: xs)
              = throwAt fc (PatternsMissing (Extra.toList $ x::xs))

            zip env (x :: xs) []
              = throwAt fc (RedundantPatterns (x::xs))

            zip env (x :: xs) (y :: ys)
              = do rest <- zip env xs ys
                   pure (Lambda.extend rest x y)

    check env er ec p ret type (Cond fc cond tt ff)
      = do tm <- check fc env BOOL cond

           R tyL uL tmL <- check env er ec p ret type tt
           R tyR uR tmR <- check env er ec p ret type ff

           pure (R (Choices [B "true" UNIT tyL, B "false" UNIT tyR])
                   (Choices [uL, uR])
                   (Cond tm tmL  tmR)
                )

    check env er ec p ret ptype (Match fc cond prf (c::cs))
      = do (UNION ((es,et) ::: fs) ** tm) <- synth env cond
               | (ty ** _) => throwAt fc (UnionExpected ty)

           C  l  p  a  <- case' fc ret es et c
           CS ls ps as <- cases fc ret  fs   cs

           pure (Check.R (Choices (B es et l::ls))
                   (Choices (p::ps))
                   (Match tm (a::as))
                         -- (Match tm (a::as))
                   )

      where case' : (fc   : FileContext)
                 -> (ret  : Base)
                 -> (expL : String)
                 -> (et   : Base)
                 -> (o    : Offer oraw)
                         -> Capable (Check.Case.Result roles rs ds ss gs ks ls p (expL,et) ptype ret)
            case' fc ret el et (O fc' l' mn cont)
              = do Refl <- embedAt fc' (WrongLabel el l')
                                       (decEq el l')
                   R tySyn pU cont <- check (Lambda.extend env mn et)
                                            er ec p ret ptype cont

                   pure (C tySyn pU (C el cont))

            cases : (fc  : FileContext)
                 -> (ret : Base)
                 -> (bs  : List (Pair String Base))
                 -> (os  : Vect.Quantifiers.All.All Offer as')
                        -> Capable (Check.Cases.Result roles rs ds ss gs ks ls p bs ptype ret)

            cases fc _ Nil Nil
              = pure (CS Nil Nil Cases.Nil)

            cases fc _ Nil os
              = throwAt fc (RedundantCases (flattern os))

            cases fc _ bs Nil
              = throwAt fc (CasesMissing bs)

            cases fc ret (MkPair l t::bs) (o::os)
              = do C  lSyn  pU  o  <- case' fc ret l t o
                   CS lSyns pUs os <- cases fc ret bs os
                   pure (CS (B l t lSyn::lSyns)
                            (pU::pUs)
                            (o::os))

    -- [ NOTE ] Holes are only checkable terms as they inherit the checked types.
    check env er ec princ ret type (Hole ref prf)
      = showHoleSessionExit (lambda env)
                                  er
                                  ec
                                  type
                                  (get ref)

    check e er ec p ret type term
      = do R syn tm <- tryCatch (synth e er ec p ret term)

                                (\eer => throwAt (getFC term) (IllTypedSession (unlines [toString ec er type
                          , "but could not synthesis given type because of\n\n\{show eer}."])))

           let msg = unlines [ toString ec er type
                             , "but given:\n\t\{toString ec er syn}"]
           throwAt (getFC term) (IllTypedSession msg)


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

       (p ** principle) <- synth rh prin

       (tyARGS ** as) <- args (delta env) as

       (tyRET ** ret) <- synth (delta env) ret

       (tyLocal ** tm) <- embedAt fc
                                  (ProjectionError) -- @TODO Error messages.
                                  (Projection.Closed.project principle tyGlobal)

       R tyLocal' prf tm <- assert_total -- @TODO this is bad, but the
                                         -- totality hcecker is
                                         -- throwing an error where
                                         -- there _should not_ be one.
                            $ check ({ lambda := expand as} env)
                                    rh
                                    Nil
                                    principle
                                    tyRET
                                    tyLocal
                                    scope

       pure (SESH rh principle tyLocal' tyARGS tyRET ** Sesh tm)

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
