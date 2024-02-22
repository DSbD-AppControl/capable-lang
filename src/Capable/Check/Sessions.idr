||| Type-checker for sessions.
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Capable.Check.Sessions

import Data.String
import Toolkit.Data.Location
import Toolkit.Data.DList.All
import Capable.Types
import Capable.Types.Protocol.Projection
import Capable.Types.Protocol.Merge
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
import Capable.State

%hide Capable.State.State.roles

%default total

namespace Expr
  namespace Check


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
          C : (given : Branch Local.Local ks rolez (l,t))
           -> (expr : Case rolez rs ds ss gs ls ks ret p (l,t) given)
                  -> Result rolez rs ds ss gs ks ls p (l,t) expected ret

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
                 -> (e    : (String, Base))
                 -> (ret  : Base)
                         -> Type
        where
          O : (given : Branch Local.Local ks rolez (l',t'))
           -> (prf   : Subset ks rolez
                              Subset
                              given
                              expected)
           -> (expr : Offer  rolez rs ds ss gs ls ks ret p given)
                   -> Result rolez rs ds ss gs ks ls p expected (l',t') ret

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
          CS : (given : Local.Branches ks rolez lts)
            -> (expr  : Cases  rolez rs ds ss gs ls ks ret p lts given)
                     -> Result rolez rs ds ss gs ks ls p lts expected ret

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
                 -> (lts' : List (String, Base))
                 -> (ret  : Base)
                         -> Type
        where
          OS : (given  : Local.Branches ks rolez ltsA)
            -> (prf  : Offer.Subset ks rolez Protocol.Subset given expected)
            -> (expr : Offers rolez rs ds ss gs ls ks ret p given)
                    -> Result rolez rs ds ss gs ks ls p expected ltsA ret

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
      R : (l    : Local ks rolez)
       -> (expr : Expr   rolez rs ds ss gs ls ks p l ret)
               -> Result rolez rs ds ss gs ks ls p ret

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
        C : (b    : Branch Local ks rolez (s,t))
         -> (expr : Case rolez rs ds ss gs ls ks ret p (s,t) b)
                -> Result rolez rs ds ss gs ks ls p (s,t) ret

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
         -> (bs   : Local.Branches ks rolez lts)
         -> (expr : Cases rolez rs ds ss gs ls ks ret p lts bs)
                 -> Result rolez rs ds ss gs ks ls p lts ret
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
        O : (b    : Branch Local ks rolez (s,t))
         -> (expr : Offer rolez rs ds ss gs ls ks ret p b)
                -> Result rolez rs ds ss gs ks ls p (s,t) ret

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
        OS : (bs   : Local.Branches ks rolez lts)
         -> (expr : Offers rolez rs ds ss gs ls ks ret p bs)
                 -> Result rolez rs ds ss gs ks ls p lts ret

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
        R : (given  : Local ks rolez)
         -> (prf    : Subset given expected)
         -> (expr : Expr   rolez rs ds ss gs ls ks p given ret)
                 -> Result rolez rs ds ss gs ks ls p expected ret

namespace Expr

  namespace Synth
    export
    synth : {e, rolez, ls, ks : _}
         -> {rs    : List Ty.Role}
         -> {ds    : List Ty.Base}
         -> {gs    : List Ty.Method}
         -> {ss    : List Ty.Session}
         -> State
         -> (env   : Env rs ds ss gs ls)
         -> (enr   : Context Role rolez)
         -> (enc   : Context Protocol.Kind ks)
         -> (princ : DeBruijn.Role rolez p')
         -> (ret   : Base)
         -> (expr  : Sessions.Expr e)
                  -> Capable (State, Synth.Result rolez rs ds ss gs ks ls princ ret)

  namespace Check
    export
    check : {e, roles, ls,ks : _}
         -> {rs   : List Ty.Role}
         -> {ds   : List Ty.Base}
         -> {gs   : List Ty.Method}
         -> {ss   : List Ty.Session}
         -> State
         -> (env  : Env rs ds ss gs ls)
         -> (enr  : Context Role roles)
         -> (enc  : Context Protocol.Kind ks)
         -> (princ : DeBruijn.Role roles p)
         -> (ret  : Base)
         -> (type : Local.Local ks roles)
         -> (expr : Sessions.Expr e)
                 -> Capable (State ,Check.Result roles rs ds ss gs ks ls princ type ret)



    -- [ NOTE ] Session Typed Terms

  namespace Synth
    synth st env er ec p ret (Hole ref prf)
      = unknown (span ref)

    synth st env er ec p ret (Call fc ref)
      = do (r ** idx) <- lookup ec (MkRef fc ref)
           -- @TODO change to ref

           pure (st, (R (Call idx) (Call idx)))

    synth st env er ec p ret (Crash fc expr)
      = do (st, tm) <- check st fc env ret expr
           pure (st, R Crash (Crash tm))

    synth st env er ec p ret (End fc expr)

      = do (st, tm) <- check st fc env ret expr
           pure (st, R End (End tm))

    synth st env er ec p ret (Cond fc cond tt ff)
      = do (st, tm) <- check st fc env BOOL cond
           (st, R tyT tmT) <- synth st env er ec p ret tt
           (st, R tyF tmF) <- synth st env er ec p ret ff

           (lty ** prfMerge) <- embedAt fc
                                        (MergeError (unlines [toString ec er tyT, toString ec er tyF]))
                                        (Protocol.merge tyT tyF)

           pure (st, R lty (Cond tm tmT tmF prfMerge))

    synth st env er ec p ret (Match fc cond prf (c::cs))
      = do (st, (UNION ((es,et) ::: fs) ** tm)) <- synth st env cond
               | (st, (ty ** _)) => throwAt fc (UnionExpected ty)

           (st, C  b  a)  <- case' st fc ret es et c
           (st, CS bs as) <- cases st fc ret  fs   cs

           (lty ** prfMerge) <- embedAt fc
                                        (MergeError (unlines $ mapToList (\(B _ _ c) => toString ec er c) (b::bs)))
                                        (Many.merge (b::bs))

           pure (st,
                 R lty
                   (Match tm (a::as) prfMerge)
                   )

      where case' : State
                 -> (fc   : FileContext)
                 -> (ret  : Base)
                 -> (expL : String)
                 -> (et   : Base)
                 -> (o    : Offer oraw)
                         -> Capable (State, Case.Result rolez rs ds ss gs ks ls p (expL,et) ret)
            case' st fc ret el et (O fc' l' mn cont)
              = do Refl <- embedAt fc' (WrongLabel el l')
                                       (decEq el l')
                   (st, R local cont) <- synth st
                                               (Lambda.extend env mn et)
                                                 er ec p ret cont
                   pure (st, C (B el et local) (C el cont))

            cases : State
                 -> (fc : FileContext)
                 -> (ret : Base)
                 -> (bs : List (String,Base))
                 -> (os : Vect.Quantifiers.All.All Offer as')
                       -> Capable (State, Cases.Result rolez rs ds ss gs ks ls p bs ret)
            cases st fc _ Nil Nil
              = pure (st, CS Nil Nil)

            cases _ fc _ Nil os
              = throwAt fc (RedundantCases (flattern os))

            cases _ fc _ bs Nil
              = throwAt fc (CasesMissing bs)

            cases st fc ret ((expL,expTy)::bs) (o::os)
              = do (st, C (B l t b) o') <- case' st fc ret expL expTy o
                   (st, CS bs os) <- cases st fc ret bs os

                   pure (st, CS (B l t b::bs) ((::) o' os))


    synth st env er ec p ret (LetRec fc s scope)
      = do (st, R l tm) <- synth st env er (I s (R s) :: ec) p ret scope
           pure (st, R (Rec _ l) (LetRec tm))


    synth st env er ec p ret (Read fc r ty prf (ofs::offs) onEr)
        = do (UNION ((es,et) ::: fs) ** _) <- synth (delta env) ty
               | (ty ** _) => throwAt fc (UnionExpected ty)

             prfM <- embedAt fc (\prf => NotMarshable (UNION ((es,et):::fs)) prf)
                                (marshable (UNION ((es,et):::fs)))

             (r' ** target) <- synth er r

             (st, O  b  o   ) <- offer  st fc ret es et ofs
             (st, OS bs offs) <- offers st fc ret   fs  offs

             (st, R Crash err)  <- synth st env er ec p ret onEr
                | (_, R type _) => throwAt fc (IllTypedSession ("Crash") (toString ec er type))

             pure ( st
                  , R (ChoiceL BRANCH
                              target
                              (Val (UNION ((es,et) ::: fs)))
                              prfM
                              (b::bs)
                                           )
                            (Read target prfM (o::offs) err))

        where offer : State
                   -> (fc   : FileContext)
                   -> (ret  : Base)
                   -> (expL : String)
                   -> (et   : Base)
                   -> (o    : Offer oraw)
                           -> Capable (State, Offer.Result rolez rs ds ss gs ks ls p (expL,et) ret)
              offer st fc ret expL expTy (O fc' l' mname cont)
                = do Refl <- embedAt fc' (WrongLabel expL l')
                                         (decEq expL l')
                     (st, R local cont) <- synth st (Lambda.extend env mname expTy)
                                                 er ec p ret cont
                     pure (st, O (B expL expTy local) (O expL cont))


              offers : State
                    -> (fc : FileContext)
                    -> (ret : Base)
                    -> (bs : List (String,Base))
                    -> (os : Vect.Quantifiers.All.All Offer as')
                          -> Capable (State, Synth.Offers.Result rolez rs ds ss gs ks ls p bs ret)
              offers st fc _ Nil Nil
                = pure (st, OS Nil Nil)

              offers st fc _ Nil os
                = throwAt fc (RedundantCases (flattern os))

              offers st fc _ bs Nil
                = throwAt fc (CasesMissing bs)

              offers st fc ret ((expL,expTy)::bs) (o::os)
                = do (st, O (B l t b) o') <- offer st fc ret expL expTy o
                     (st, OS bs os) <- offers st fc ret bs os

                     pure (st, OS (B l t b::bs) ((::) o' os))


    synth st env er ec p ret (Send fc role tyTm label msg scope onErr)
      = do -- 1. Check the type of the annotation

           (UNION ((es,et) ::: fs) ** cond) <- synth (delta env) tyTm
             | (ty ** _) => throwAt fc (UnionExpected ty)

           -- 2. Get the role.
           (r ** target) <- synth er role

           -- 3. Get the type of the payload.
           (st, (tyM' ** tmM)) <- synth st env msg

           -- 4. Check if marshable
           prfM <- embedAt fc (NotMarshable tyM')
                              (marshable tyM')

           -- 5. Check is value tag.
           (ty ** loc) <- isElem fc fc label ((es,et)::fs)

           (st, R lsytn rest) <- synth st env er ec p ret scope

           (st, R Crash err)  <- synth st env er ec p ret onErr
              | (st, R type _) => throwAt fc (IllTypedSession "Crash" (toString ec er type))

           pure (st, R (ChoiceL SELECT
                            target
                            (Val (UNION ((label,tyM'):::Nil)))
                            (UNION [F label prfM])
                            ([B label tyM' lsytn]))
                   (Send target label tmM prfM rest err))

    -- [ NOTE ] Non-Session-Typed Terms

    synth st env er ec p ret (Seq fc x y)
      = do (st, tmL) <- check st fc env UNIT x
           (st, R l tmR) <- synth st env er ec p ret y
           pure (st, R l (Seq tmL tmR))

    synth st env er ec p ret (LetTy fc ref k ty val scope)
      = do (st, (tyVal ** T tyTmVal val)) <- check st fc env ty val

           case k of
             HEAP
               => do (st, R l scope) <- synth st
                                              (Lambda.extend env ref (REF tyVal))
                                              er
                                              ec
                                              p
                                              ret
                                              scope

                     pure (st, R _ (Let (TyRef tyTmVal) (Builtin Alloc [val]) scope))
             STACK
               => do (st, R l scope) <- synth st
                                              (Lambda.extend env ref tyVal)
                                              er
                                              ec
                                              p
                                              ret
                                              scope

                     pure (st, R _ (Let tyTmVal val scope))

    synth st env er ec p ret (Let fc ref k val scope)
        = do (st, (tyVal ** T tyTmVal val)) <- synthReflect st env val

             case k of
               HEAP
                 => do (st, R l scope) <- synth st
                                                (Lambda.extend env ref (REF tyVal))
                                                 er
                                                 ec
                                                 p
                                                 ret
                                                 scope

                       pure (st, R l (Let (TyRef tyTmVal) (Builtin Alloc [val]) scope))
               STACK
                 => do (st, R l scope) <- synth st
                                                (Lambda.extend env ref tyVal)
                                               er
                                               ec
                                               p
                                               ret
                                               scope

                       pure (st, R l (Let tyTmVal val scope))

    synth st env er ec p ret (Split fc this val scope)
        = do (st, (TUPLE (f::s::ts) ** v)) <- synth st env val
               | (st, (tyV ** _)) => throwAt fc (PairExpected tyV)

             envExt <- zip env this (f::s::ts)

             (st, R l rest) <- synth st envExt er ec p ret scope

             pure (st, R l (Split v rest))

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


namespace Expr

  namespace Check

    -- [ NOTE ] Session Typed Terms
    --
    check st e er ec p ret End (End fc expr)
      = do (st, tm) <- check st fc e ret expr
           pure (st, R End End (End tm))

    --
    check st e er ec p ret Crash (Crash fc expr)
      = do (st, tm) <- check st fc e ret expr
           pure (st, R Crash Crash (Crash tm))

    --
    check st e er ec princ ret (Call x) (Call fc ref)
      = do (r ** idx) <- lookup ec (MkRef fc ref)
           -- @TODO change to ref

           Same Refl Refl <- embedAt fc
                                     (MismatchK (reflect ec x) ref)
                                     (Index.decEq x idx)

           pure (st, R (Call idx) Call (Call idx))


    --
    check st e er ec p ret (Rec l type) (LetRec fc s scope)
      = do (st, R lsyn prf tm) <- check st e
                                  er
                                  (I s l :: ec)
                                  p
                                  ret
                                  type
                                  scope

           pure (st, R (Rec _ lsyn) (Rec prf) (LetRec tm))


    --
    check st e er ec p ret (ChoiceL BRANCH whom (Val (UNION ((l,t):::fs)))
                                                  (UNION (m::ms))
                                                         (B l t c::cs))
                           (Read fc role tyTm _ (o::os) onErr)

      = do -- 1. Check the type of the annotation

           (UNION ((lf,tf) ::: fields) ** tyTm) <- synth (delta e) tyTm
             | (ty ** _) => throwAt fc (UnionExpected ty)

           prfM <- embedAt fc (\prf => NotMarshable (UNION ((lf,tf):::fields)) prf)
                              (marshable (UNION ((lf,tf):::fields)))


           -- 2. Check that the role is correct
           (r ** target) <- synth er role

           Same Refl Refl <- embedAt fc
                                     (MismatchRoleS (let R s = role in s)
                                                    (reflect er whom))
                                     (Index.decEq whom target)

           -- 3. Check the branches
           (st, O  synO  prfO  o)  <- offer  st fc ret (B l t c) (lf,tf) o
           (st, OS synOS prfOS os) <- offers st fc ret        cs fields  os

           -- 4. check the error branch
           (st, R Crash Crash onErr) <- check st e er ec p ret Crash onErr

           -- 5. Return Evidence
           pure (st, Check.R
                   (ChoiceL BRANCH
                            target
                            (Val (UNION ((lf,tf):::fields)))
                            prfM
                            (synO::synOS))
                   (Offer (Next prfO prfOS))
                   (Read target
                         prfM
                         (o::os)
                         onErr)
                   )

        where offer : State
                   -> (fc  : FileContext)
                   -> (ret : Base)
                   -> (b   : Branch Local.Local ks roles (le,te))
                   -> (e   : (String, Base))
                   -> (o   : Offer oraw)
                          -> Capable (State, Check.Offer.Result roles rs ds ss gs ks ls p b e ret)
              offer st fc ret (B lg tg tyC) (l,te) (O fc' l' m cont)
                = do Refl <- embedAt fc' (WrongLabel lg l')
                                         (decEq lg l')
                     Refl <- embedAt fc' (WrongLabel l l')
                                         (decEq l l')

                     Refl <- compare fc' tg te

                     (st, R tySyn pU tm) <- check st (Lambda.extend e m te)
                                            er
                                            ec
                                            p
                                            ret
                                            tyC
                                            cont
                     pure (st, Check.Offer.O
                             (B l te tySyn)
                             (B Refl Refl pU) -- (B pU)
                             (O l tm) -- (O l tm)
                             )

              offers : State
                    -> (fc  : FileContext)
                    -> (ret : Base)
                    -> (bs  : Local.Branches ks roles bs')
                    -> (ls'  : List (String, Base))
                    -> (os  : Vect.Quantifiers.All.All Offer as')
                           -> Capable (State, Check.Offers.Result roles rs ds ss gs ks ls p bs ls' ret)

              offers st fc _ Nil Nil Nil
                = pure (st, OS Nil Empty Offers.Nil)

              offers _ fc _ Nil _ os
                = throwAt fc (RedundantCases (flattern os))

              offers _ fc _ bs _ Nil
                = do let Val bs = getLTs bs
                     throwAt fc (CasesMissing bs)

              offers st fc ret ((B l t b)::bs) (a::as) (o::os)
                = do (st, O  lSyn  pU  o ) <- offer  st fc ret (B l t b) a  o
                     (st, OS lSyns pUs os) <- offers st fc ret bs        as os
                     pure (st, OS (lSyn::lSyns)
                              (Next pU pUs)
                              (o::os))

              offers _ fc _ (b::bs) Nil (o::os)
                = do let Val bs = getLTs bs
                     throwAt fc (CasesMissing bs)

    --
    check st e er ec p ret (ChoiceL SELECT whom (Val (UNION (f:::fs)))
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

           R tyM tyC (F label prfM) sel <- Decidable.embedAt fc (LabelMismatch label
                                                                  (map fst $ f::fs))
                                                      (select label (m::ms) (c::cs))

           (st, tmM) <- check st fc e tyM msg

           -- 4. Get the type(s) for the remainder of the protocol

           (st,  R tySyn pU scope) <- check st e er ec p ret tyC scope

           (st, R Crash Crash onErr) <- check st e er ec p ret Crash onErr

           -- 5. Is it a valid selection?

           -- @TODO merge into Selection stuff
           prfS <- embedAt
                     fc
                     (SubsetError (toString ec er $ [B label tyM tySyn])
                                  (toString ec er $ (c::cs))
                                  )

                     (Select.subset subset
                                    [B label tyM tySyn]
                                    (c::cs))

           -- 6. Return Evidence

           pure (st, R (ChoiceL SELECT
                            target
                            (Val (UNION ((label,tyM):::Nil)))
                            (UNION (F label prfM::Nil))
                            (B label tyM tySyn::Nil))
                   (Select prfS)
                   (Send target label tmM prfM scope onErr))

    -- [ NOTE ] Non-Session Typed Terms

    check st e er ec p ret type (Seq fc x y)

      = do (st, tmL) <- check st fc e UNIT x
           (st, R lSyn pU tmR) <- check st e er ec p ret type y
           pure (st, R lSyn pU (Seq tmL tmR))

    --
    check st e er ec p ret type (LetTy fc ref k ty val scope)
      = do (st, (tyVal ** T tyTmVal val)) <- check st fc e ty val

           case k of
             HEAP
               => do (st, R lSyn pU scope) <- check st
                                              (Lambda.extend e ref (REF tyVal))
                                              er
                                              ec
                                              p
                                              ret
                                              type
                                              scope

                     pure (st, R lSyn pU (Let (TyRef tyTmVal) (Builtin Alloc [val]) scope))
             STACK
               => do (st, R lSyn pU scope) <- check st (Lambda.extend e ref tyVal)
                                              er
                                              ec
                                              p
                                              ret
                                              type
                                              scope

                     pure (st, R lSyn pU (Let tyTmVal val scope))

    check st e er ec p ret type (Let fc ref k val scope)
      = do (st, (tyVal ** T tyTmVal val)) <- synthReflect st e val

           case k of
             HEAP
               => do (st, R l pU scope) <- check st (Lambda.extend e ref (REF tyVal))
                                               er
                                               ec
                                               p
                                               ret
                                               type
                                               scope

                     pure (st, R l pU (Let (TyRef tyTmVal) (Builtin Alloc [val]) scope))
             STACK
               => do (st, R l pU scope) <- check st (Lambda.extend e ref tyVal)
                                             er
                                             ec
                                             p
                                             ret
                                             type
                                             scope

                     pure (st, R l pU (Let tyTmVal val scope))

    check st e er ec p ret type (Split fc this val scope)

      = do (st, (TUPLE (f::s::ts) ** v)) <- synth st e val
             | (st, (tyV ** _)) => throwAt fc (PairExpected tyV)

           envExt <- zip e this (f::s::ts)

           (st, R l p rest) <- check st envExt er ec p ret type scope

           pure (st, R l p (Split v rest))

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


    check st env er ec p ret type (Cond fc cond tt ff)
      = do (st, tm) <- check st fc env BOOL cond

           (st, R tyL _ tmL) <- check st env er ec p ret type tt
           (st, R tyR _ tmR) <- check st env er ec p ret type ff

           (lty ** prfMerge) <- embedAt fc
                                        (MergeError (unlines [toString ec er tyL, toString ec er tyR]))
                                        (Protocol.merge tyL tyR)


           prfS <- embedAt
                     fc
                     (SubsetError (toString ec er lty)
                                  (toString ec er type))
                     (subset lty type)


           pure (st, R lty
                   prfS
                   (Cond tm tmL tmR prfMerge)
                )

    check st env er ec p ret ptype (Match fc cond prf (c::cs))
      = do (st, (UNION ((es,et) ::: fs) ** tm)) <- synth st env cond
               | (st, (ty ** _)) => throwAt fc (UnionExpected ty)

           (st, C  tyC  c ) <- case' st fc ret es et c
           (st, CS tyCS cs) <- cases st fc ret  fs   cs

           (lty ** prfMerge) <- embedAt
                                  fc
                                  (MergeError
                                    (unlines
                                     $ mapToList (\(B _ _ c) => toString ec er c)
                                                 (tyC::tyCS)))
                                  (Many.merge (tyC::tyCS))

           prfS <- embedAt
                     fc
                     (SubsetError (toString ec er lty)
                                  (toString ec er ptype))
                     (subset lty ptype)

           pure (st, Check.R
                   lty
                   prfS
                   (Match tm
                          (c::cs)
                          prfMerge)

                   )

      where case' : State
                 -> (fc   : FileContext)
                 -> (ret  : Base)
                 -> (expL : String)
                 -> (et   : Base)
                 -> (o    : Offer oraw)
                         -> Capable (State, Check.Case.Result roles rs ds ss gs ks ls p (expL,et) ptype ret)
            case' st fc ret el et (O fc' l' mn cont)
              = do Refl <- embedAt fc' (WrongLabel el l')
                                       (decEq el l')
                   (st, R tySyn pU cont) <- check st (Lambda.extend env mn et)
                                            er ec p ret ptype cont

                   pure (st, C (B el et tySyn)
                           (C el cont))

            cases : State
                 -> (fc  : FileContext)
                 -> (ret : Base)
                 -> (bs  : List (Pair String Base))
                 -> (os  : Vect.Quantifiers.All.All Offer as')
                        -> Capable (State, Check.Cases.Result roles rs ds ss gs ks ls p bs ptype ret)

            cases st fc _ Nil Nil
              = pure (st, CS Nil Cases.Nil)

            cases _ fc _ Nil os
              = throwAt fc (RedundantCases (flattern os))

            cases _ fc _ bs Nil
              = throwAt fc (CasesMissing bs)

            cases st fc ret (MkPair l t::bs) (o::os)
              = do (st, C  lSyn  o ) <- case' st fc ret l t o
                   (st, CS lSyns os) <- cases st fc ret bs os
                   pure (st, CS (lSyn::lSyns)
                            (o::os))

    -- [ NOTE ] Holes are only checkable terms as they inherit the checked types.
    check st env er ec princ ret type (Hole ref prf)
        = do let st = addHole st (get ref) (HSesh (span ref) env er ec type princ (get ref))

             -- Uck.
             prf <- embedAt (span ref)
                            (SubsetError (toString ec er type)
                                         (toString ec er type))
                            (subset type type)

             pure (st, R type prf $ Hole (get ref))
--      = showHoleSessionExit (lambda env)
--                                  er
--                                  ec
--                                  type
--                                  (get ref)

    check st e er ec p ret type term

      = do (st, R syn tm) <- tryCatch (synth st e er ec p ret term)

                                (\eer => throwAt (getFC term)
                                          (IllTypedSession (toString ec er type)
                                                           (show eer)))

           prf <- embedAt (getFC term)
                          (SubsetError (toString ec er type)
                                       (toString ec er syn))
                          (subset syn type)

           pure (st, R syn prf tm)



checkHoles : {e, roles, ls,ks : _}
          -> {rs   : List Ty.Role}
          -> {ds   : List Ty.Base}
          -> {gs   : List Ty.Method}
          -> {ss   : List Ty.Session}
          -> State
          -> (env  : Env rs ds ss gs ls)
          -> (enr  : Context Role roles)
          -> (enc  : Context Protocol.Kind ks)
          -> (princ : DeBruijn.Role roles p)
          -> (ret  : Base)
          -> (type : Local.Local ks roles)
          -> (expr : Sessions.Expr e)
                  -> Capable (State, Check.Result roles rs ds ss gs ks ls princ type ret)
checkHoles st e er ec p ret type term

  = tryCatch (do (st, R syn tm) <- synth st e er ec p ret term

                 prf <- embedAt (getFC term)
                                (SubsetError (toString ec er type)
                                             (toString ec er syn))
                                (subset syn type)

                 pure (st, R syn prf tm))

             (const $ check st e er ec p ret type term)




export
synth : {rs   : List Ty.Role}
     -> {ds   : List Ty.Base}
     -> {gs   : List Ty.Method}
     -> {ss   : List Ty.Session}
     -> State
     -> (env  : Env rs ds ss gs Nil)
     -> (sesh : Session s)
             -> Capable (State, DPair Ty.Method (Session rs ds ss gs))
synth st env (Sesh fc prin ref p prf as ret scope)
  = do (S rh tyGlobal ** prot) <- Sigma.lookup env ref

       (p ** principle) <- synth rh prin

       (tyARGS ** as) <- args (delta env) as

       (tyRET ** ret) <- synth (delta env) ret

       (tyLocal ** prfProj) <- embedAt fc
                                  (ProjectionError) -- @TODO Error messages.
                                  (Projection.Closed.project principle tyGlobal)

       (st, R tyLocal' prf tm) <- checkHoles st
                                    ({ lambda := expand as} env)
                                    rh
                                    Nil
                                    principle
                                    tyRET
                                    tyLocal
                                    scope

       pure (st, (SESH rh principle tyLocal tyARGS tyRET ** Sesh prot prfProj prf tm))

namespace Raw
  export
  synth : {rs  : List Ty.Role}
       -> {ds  : List Ty.Base}
       -> {gs  : List Ty.Method}
       -> {ss  : List Ty.Session}
       -> State
       -> (env : Env rs ds ss gs Nil)
       -> (syn : AST SESH)
              -> Capable (State, DPair Ty.Method (Session rs ds ss gs))
  synth st env s
    = synth st env (toSession s)
-- [ EOF ]
