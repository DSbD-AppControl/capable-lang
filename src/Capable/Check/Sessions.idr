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
          C : (given : Branch Local.Local ks roles (l,t))
           -> (expr : Case roles rs ds ss gs ls ks ret p (l,t) given)
                  -> Result roles rs ds ss gs ks ls p (l,t) expected ret

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
          O : (given : Branch Local.Local ks roles (l',t'))
           -> (prf   : Subset ks roles
                              Subset
                              given
                              expected)
           -> (expr : Offer  roles rs ds ss gs ls ks ret p given)
                   -> Result roles rs ds ss gs ks ls p expected (l',t') ret

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
          CS : (given : Local.Branches ks roles lts)
            -> (expr  : Cases  roles rs ds ss gs ls ks ret p lts given)
                     -> Result roles rs ds ss gs ks ls p lts expected ret

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
          OS : (given  : Local.Branches ks roles ltsA)
            -> (prf  : Offer.Subset ks roles Protocol.Subset given expected)
            -> (expr : Offers roles rs ds ss gs ls ks ret p given)
                    -> Result roles rs ds ss gs ks ls p expected ltsA ret

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
      R : (l    : Local ks roles)
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
        C : (b    : Branch Local ks roles (s,t))
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
         -> (bs   : Local.Branches ks roles lts)
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
        O : (b    : Branch Local ks roles (s,t))
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
        OS : (bs   : Local.Branches ks roles lts)
         -> (expr : Offers roles rs ds ss gs ls ks ret p bs)
                 -> Result roles rs ds ss gs ks ls p lts ret

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
        R : (given  : Local ks roles)
         -> (prf    : Subset given expected)
         -> (expr : Expr   roles rs ds ss gs ls ks p given ret)
                 -> Result roles rs ds ss gs ks ls p expected ret

namespace Expr

  namespace Synth
    export
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

  namespace Check
    export
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

  namespace Synth
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

           (lty ** prfMerge) <- embedAt fc
                                        (MergeError (unlines [toString ec er tyT, toString ec er tyF]))
                                        (Protocol.merge tyT tyF)

           pure (R lty (Cond tm tmT tmF prfMerge))

    synth env er ec p ret (Match fc cond prf (c::cs))
      = do (UNION ((es,et) ::: fs) ** tm) <- synth env cond
               | (ty ** _) => throwAt fc (UnionExpected ty)

           C  b  a  <- case' fc ret es et c
           CS bs as <- cases fc ret  fs   cs

           (lty ** prfMerge) <- embedAt fc
                                        (MergeError (unlines $ mapToList (\(B _ _ c) => toString ec er c) (b::bs)))
                                        (Many.merge (b::bs))

           pure (R lty
                   (Match tm (a::as) prfMerge)
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

             pure (R (ChoiceL BRANCH
                              target
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

           pure (R (ChoiceL SELECT
                            target
                            (Val (UNION ((label,tyM'):::Nil)))
                            (UNION [F label prfM])
                            ([B label tyM' lsytn]))
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


namespace Expr

  namespace Check

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
    check e er ec p ret (ChoiceL BRANCH whom (Val (UNION ((l,t):::fs)))
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
           O  synO  prfO  o  <- offer  fc ret (B l t c) (lf,tf) o
           OS synOS prfOS os <- offers fc ret        cs fields  os

           -- 4. check the error branch
           R Crash Crash onErr <- check e er ec p ret Crash onErr

           -- 5. Return Evidence
           pure (Check.R
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

        where offer : (fc  : FileContext)
                   -> (ret : Base)
                   -> (b   : Branch Local.Local ks roles (le,te))
                   -> (e   : (String, Base))
                   -> (o   : Offer oraw)
                          -> Capable (Check.Offer.Result roles rs ds ss gs ks ls p b e ret)
              offer fc ret (B lg tg tyC) (l,te) (O fc' l' m cont)
                = do Refl <- embedAt fc' (WrongLabel lg l')
                                         (decEq lg l')
                     Refl <- embedAt fc' (WrongLabel l l')
                                         (decEq l l')

                     Refl <- compare fc' tg te

                     R tySyn pU tm <- check (Lambda.extend e m te)
                                            er
                                            ec
                                            p
                                            ret
                                            tyC
                                            cont
                     pure (Check.Offer.O
                             (B l te tySyn)
                             (B Refl Refl pU) -- (B pU)
                             (O l tm) -- (O l tm)
                             )

              offers : (fc  : FileContext)
                    -> (ret : Base)
                    -> (bs  : Local.Branches ks roles bs')
                    -> (ls'  : List (String, Base))
                    -> (os  : Vect.Quantifiers.All.All Offer as')
                           -> Capable (Check.Offers.Result roles rs ds ss gs ks ls p bs ls' ret)

              offers fc _ Nil Nil Nil
                = pure (OS Nil Empty Offers.Nil)

              offers fc _ Nil _ os
                = throwAt fc (RedundantCases (flattern os))

              offers fc _ bs _ Nil
                = do let Val bs = getLTs bs
                     throwAt fc (CasesMissing bs)

              offers fc ret ((B l t b)::bs) (a::as) (o::os)
                = do O  lSyn  pU  o  <- offer  fc ret (B l t b) a  o
                     OS lSyns pUs os <- offers fc ret bs        as os
                     pure (OS (lSyn::lSyns)
                              (Next pU pUs)
                              (o::os))

              offers fc _ (b::bs) Nil (o::os)
                = do let Val bs = getLTs bs
                     throwAt fc (CasesMissing bs)

    --
    check e er ec p ret (ChoiceL SELECT whom (Val (UNION (f:::fs)))
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

           tmM <- check fc e tyM msg

           -- 4. Get the type(s) for the remainder of the protocol

           R tySyn pU scope <- check e er ec p ret tyC scope

           R Crash Crash onErr <- check e er ec p ret Crash onErr

           -- 5. Is it a valid selection?

           -- @TODO merge into Selection stuff
           prfS <- embedAtInfo
                     fc
                     (IllTypedSession "Subset error for seelction")
                     (Select.subset subset
                                    [B label tyM tySyn]
                                    (c::cs))

           -- 6. Return Evidence

           pure (R (ChoiceL SELECT
                            target
                            (Val (UNION ((label,tyM):::Nil)))
                            (UNION (F label prfM::Nil))
                            (B label tyM tySyn::Nil))
                   (Select prfS)
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

           R tyL _ tmL <- check env er ec p ret type tt
           R tyR _ tmR <- check env er ec p ret type ff

           (lty ** prfMerge) <- embedAt fc
                                        (MergeError (unlines [toString ec er tyL, toString ec er tyR]))
                                        (Protocol.merge tyL tyR)


           prfS <- embedAtInfo
                     fc
                     (IllTypedSession "Subset error for seelction")
                     (subset lty type)


           pure (R lty
                   prfS
                   (Cond tm tmL tmR prfMerge)
                )

    check env er ec p ret ptype (Match fc cond prf (c::cs))
      = do (UNION ((es,et) ::: fs) ** tm) <- synth env cond
               | (ty ** _) => throwAt fc (UnionExpected ty)

           C  tyC  c  <- case' fc ret es et c
           CS tyCS cs <- cases fc ret  fs   cs

           (lty ** prfMerge) <- embedAt
                                  fc
                                  (MergeError
                                    (unlines
                                     $ mapToList (\(B _ _ c) => toString ec er c)
                                                 (tyC::tyCS)))
                                  (Many.merge (tyC::tyCS))

           prfS <- embedAtInfo
                     fc
                     (IllTypedSession "Subset error for seelction")
                     (subset lty ptype)

           pure (Check.R
                   lty
                   prfS
                   (Match tm
                          (c::cs)
                          prfMerge)

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

                   pure (C (B el et tySyn)
                           (C el cont))

            cases : (fc  : FileContext)
                 -> (ret : Base)
                 -> (bs  : List (Pair String Base))
                 -> (os  : Vect.Quantifiers.All.All Offer as')
                        -> Capable (Check.Cases.Result roles rs ds ss gs ks ls p bs ptype ret)

            cases fc _ Nil Nil
              = pure (CS Nil Cases.Nil)

            cases fc _ Nil os
              = throwAt fc (RedundantCases (flattern os))

            cases fc _ bs Nil
              = throwAt fc (CasesMissing bs)

            cases fc ret (MkPair l t::bs) (o::os)
              = do C  lSyn  o  <- case' fc ret l t o
                   CS lSyns os <- cases fc ret bs os
                   pure (CS (lSyn::lSyns)
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

           prf <- embedAt (getFC term)
                          (IllTypedSession msg)
                          (subset syn type)

           pure (R syn prf tm)



checkHoles : {e, roles, ls,ks : _}
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
checkHoles e er ec p ret type term

  = tryCatch (do R syn tm <- synth e er ec p ret term
                 let msg = unlines [ toString ec er type
                                   , "but given:\n\t\{toString ec er syn}"]

                 prf <- embedAt (getFC term)
                                (IllTypedSession msg)
                                (subset syn type)

                 pure (R syn prf tm))

             (const $ check e er ec p ret type term)




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

       R tyLocal' prf tm <- checkHoles
                                    ({ lambda := expand as} env)
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
