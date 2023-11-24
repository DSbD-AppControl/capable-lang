module Capable.Synthesis

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

import Capable.Terms
import Capable.State


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
-- [ EOF ]
