module Capable.Synthesis.Sessions

import Decidable.Equality

import Data.List.Elem
import Data.List1.Elem
import Data.Vect

import public Data.Singleton

import Toolkit.Data.DList
import Toolkit.Data.DVect
import Toolkit.Data.List.AtIndex
import Toolkit.DeBruijn.Renaming

import public Capable.Bootstrap
import Capable.Types

import Capable.State
import Capable.Check.Common

import Capable.Core

import Capable.Raw.AST
import Capable.Raw.Role
import Capable.Raw.Types
import Capable.Raw.Sessions
import Capable.Raw.Exprs
import Capable.Terms.Sessions

%hide Capable.State.State.roles

data Urgh : Type where
  MkUrgh : {e : _} -> Exprs.Expr e -> Urgh

data Result : Type where
  R : {os' : _} -> (os_raw : Vect n (AST OFFER))
   -> (AsVect os' os_raw)
   -> (os     : All Offer os_raw)
             -> Result

export
synthesis : (env : Env rs ts ps gs ls)
         -> (rzz : Context Role roles)
         -> (kzz : Context Protocol.Kind ks)
         -> (who : Role roles p)
         -> (str : String)
         -> (ty  : Local.Local ks roles)
                -> Capable (DPair EXPRSESH Sessions.Expr)
synthesis env rzz kzz who str End
  = pure (_ ** Hole (emptyRef str) R)

synthesis env rzz kzz who str (Call x)
  = pure (_ ** Call emptyFC (reflect kzz x))

synthesis env rzz kzz who str (Rec v x)
  = pure (_ ** LetRec emptyFC str (Hole (emptyRef str) R))

synthesis env rzz kzz who str (ChoiceL BRANCH whom
                                      (Val (UNION ((l,b):::eek)))
                                      prfM
                                      (B l b c :: rest))
  = do tname <- embed (Generic "Unbound type")
                      (reflectByValue (delta env) (UNION ((l,b):::eek)))
       (i ** c) <- synthesis env rzz kzz who str c
       let x = O emptyFC l (l <+> "_value") c
       R _ (prf) (os) <- buildBranches (rest)
       pure (_ ** Read emptyFC
                       (Role.R {fc = emptyFC} (reflect rzz whom))
                       (TyVar (emptyRef tname) R)
                       (Next prf)
                       (x::os)
                       (Crash emptyFC (Hole (emptyRef (str <+> "_" <+> "crash")) R))
                       )

  where
    buildBranches : DList (String, Base) (Branch (Protocol LOCAL) ks roles) u
                 -> Capable Result
    buildBranches []
      = pure (R [] Empty [])
    buildBranches ((B l1 x cont) :: xs)
      = do (i ** c) <- synthesis env rzz kzz who str cont
           let x = O emptyFC l1 (l1 <+> "_value") c
           R is ps qs <- buildBranches xs
           pure (R (_::is) (Next ps) (x::qs))

synthesis env rzz kzz who str
          (ChoiceL SELECT whom (Val (UNION ((l,b):::eek)))
                               _
                               ((B l b _) :: _))
  = do tname <- embed (Generic "Unbound type")
                      (reflectByValue (delta env) (UNION ((l,b):::eek)))
       let MkUrgh m = maybe (MkUrgh $ Raw.Exprs.Hole (emptyRef (str <+> "_" <+> "payload")) R)
                            (\n => MkUrgh $ Raw.Exprs.Var (emptyRef n) R)
                            (reflectByValue (lambda env) b )
       pure (_ ** Send emptyFC
                      (Role.R {fc = emptyFC} (reflect rzz whom))
                      (TyVar (emptyRef tname) R)
                      l
                      m
                      (Hole (emptyRef (str <+> "_" <+> "body")) R)
                      (Crash emptyFC (Hole (emptyRef (str <+> "_" <+> "crash")) R))
                      )

synthesis env rzz kzz who str Crash
  = pure (_ ** Crash emptyFC (Hole (emptyRef str) R))

-- [ EOF ]

{-
mutual

  synthesisB : {ks : _}
            -> (kctxt : Context Kind    ks)
            -> (rctxt : Context Ty.Role rs)
            -> (whom  : DeBruijn.Role rs r)
            -> (acc   : Nat)
            -> (cs    : Local.Branches ks rs lts)
                     -> Offers rs
                               Nil -- globla roles
                               Nil -- bound types
                               Nil -- protocol
                               Nil
                               l
                               ks
                               UNIT
                               whom
                               cs
  synthesisB kctxt rctxt whom acc []
    = []
  synthesisB kctxt rctxt whom acc (B l t c :: rest)
    =  O l (synthesis kctxt rctxt whom acc c)
    :: synthesisB kctxt rctxt whom acc rest



  synthesis : {ks : _}
           -> (kctxt : Context Kind    ks)
           -> (rctxt : Context Ty.Role rs)
           -> (whom  : DeBruijn.Role rs r)
           -> (acc   : Nat)
           -> (type  : Protocol LOCAL ks rs)
                    -> Expr rs
                            Nil -- globla roles
                            Nil -- bound types
                            Nil -- protocol
                            Nil
                            l
                            ks
                            whom
                            type
                            UNIT
  synthesis kctxt rctxt whom acc End
    = End (Hole ("?" <+> show acc))
  synthesis kctxt rctxt whom acc (Call x)
    = Call x
  synthesis kctxt rctxt whom acc (Rec (R v) x)
    = LetRec (synthesis (extend kctxt v (R v)) rctxt whom acc x)
  synthesis kctxt rctxt whom acc (ChoiceL BRANCH x (Val (UNION (t:::type))) prfM (c::choices))
    = Read x
           prfM
           (synthesisB kctxt rctxt whom acc (c::choices))
           (Crash (Hole ("?" <+> show acc)))

  synthesis kctxt rctxt whom acc (ChoiceL SELECT x type prfM choices)
    = Hole ("?sendGoesHere" <+> show acc)

  synthesis kctxt rctxt whom acc Crash
    = Crash (Hole ("?" <+> show acc))

export
sessionStubb : (rctxt : Context Ty.Role rs)
            -> (whom  : DeBruijn.Role rs r)
            -> (type  : Protocol LOCAL Nil rs)
                     -> Expr rs
                          Nil -- globla roles
                          Nil -- bound types
                          Nil -- protocol
                          Nil
                          Nil
                          Nil
                          whom
                          type
                          UNIT
sessionStubb rs w = synthesis Nil rs w Z

-}
