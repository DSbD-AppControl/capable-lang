|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Capable.Check.Sessions.Expr.Synth

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

-- [ EOF ]
