||| Type-checker for protocols.
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Capable.Check.Protocols

import Toolkit.Data.Location
import Toolkit.Data.DList
import Toolkit.Data.List.AtIndex

import Data.Singleton

import Capable.Types
import Capable.Core


import Capable.Raw.AST
import Capable.Raw.Role
import Capable.Raw.Types
import Capable.Raw.Exprs
import Capable.Raw.Protocols

import Capable.Check.Common
import Capable.Check.Types
import Capable.Check.Roles

import Capable.Terms.Vars
import Capable.Terms.Roles
import Capable.Terms.Types
import Capable.Terms.Protocols

%default total

mutual
  branch : {ts    : List Base}
        -> {rs    : List Ty.Role}
        -> {ks    : List Protocol.Kind}
        -> (kinds : Context Protocol.Kind    ks)
        -> (types : Context Ty.Base ts)
        -> (roles : Context Ty.Role rs)
        -> (es    : String)
        -> (eb    : Base)
        -> (bs1   : Branch b)
                 -> Capable (DPair (Branch Global ks    rs (es,eb))
                                   (Branch        ks ts rs))
  branch kinds types roles es et (B fc label type cont)
    = do Refl <- embedAt fc (WrongLabel es label) (decEq es label)

         (t ** type) <- synth types type

         Refl <- compare fc et t

         -- Here we would extend for dependent sessions...
         (g ** cont) <- synth kinds types roles cont

         pure (_ ** B es type cont)

  branches : {ts    : List Base}
          -> {rs    : List Ty.Role}
          -> {ks    : List Protocol.Kind}
          -> (kinds : Context Protocol.Kind    ks)
          -> (types : Context Ty.Base ts)
          -> (roles : Context Ty.Role rs)
          -> (fc    : FileContext)
          -> (ls    : List (String,Base))
          -> (bs1   : Vect.Quantifiers.All.All Branch bs)
                   -> Capable (DPair (Global.Branches ks    rs ls)
                                     (Branches        ks ts rs))
  branches kinds types roles _ Nil Nil
    = pure (_ ** Nil)

  branches kinds types roles fc Nil cs
    = throwAt fc (RedundantCases (flattern cs))

    where flattern : Vect.Quantifiers.All.All Branch wq -> List String
          flattern Nil = Nil
          flattern (B fc l s c :: rest)
            = l :: flattern rest

  branches kinds types roles fc es Nil
    = throwAt fc (CasesMissing es)

  branches kinds types roles fc ((l,s) :: ls) (b::bs)
    = do (tyB  ** b)  <- branch   kinds types roles    l s b
         (tyBS ** bs) <- branches kinds types roles fc ls  bs

         pure (_ ** b::bs)


  synth : {ts : List Base}
       -> {ks : List Protocol.Kind}
       -> {rs : List Ty.Role}
       -> (kinds : Context Protocol.Kind    ks)
       -> (types : Context Ty.Base ts)
       -> (roles : Context Ty.Role rs)
       -> (syn   : Protocol g)
                -> Capable (DPair (Global ks    rs)
                                  (Global ks ts rs))
  synth kinds types roles (End fc)
    = pure (_ ** End)

  synth kinds types roles (Call fc r prf)
    = do (R ** idx) <- lookup kinds r

         pure (_ ** Call idx)

  synth kinds types roles (Rec fc r prf scope)
    = do (g ** scope) <- synth (extend kinds (get r) R)
                               types
                               roles
                               scope

         pure (_ ** Rec scope)

  synth kinds types roles (Choice fc s r t prf (B1 (x::xs)))
    = do (MkRole ** stm) <- synth roles s
         (MkRole ** rtm) <- synth roles r

         (UNION ((es,et):::fs) ** tmM) <- synth types t
           | (ty ** _) => throwAt fc (UnionExpected ty)

         case marshable (UNION ((es,et):::fs)) of
           No prf _ => throwAt fc (NotMarshable (UNION ((es,et):::fs)) prf)
           Yes prfM
             => do (tyB ** tmB) <- branch kinds types roles es et x

                   (tyBs ** tmBs) <- branches kinds types roles fc fs xs

                   case Index.decEq stm rtm of
                     Yes (Same Refl Refl)
                       => do let R s' = s
                             let R r' = r
                             throwAt fc (MismatchRole (MkRef emptyFC s') (MkRef emptyFC r'))
                     No prf
                       => pure (_ ** Choice stm rtm prf tmM prfM (tmB::tmBs))

namespace View
  export
  synth : {ts : List Base}
       -> {rs : List Ty.Role}
       -> (types : Context Ty.Base ts)
       -> (roles : Context Ty.Role rs)
       -> (syn   : Protocol g)
                -> Capable (DPair (Global Nil    rs)
                              (Global Nil ts rs))
  synth types roles p
    = synth Nil types roles p

namespace Raw

  export
  synth : {ts    : List Ty.Base}
       -> {rs    : List Ty.Role}
       -> (types : Context Ty.Base ts)
       -> (roles : Context Ty.Role rs)
       -> (sesh  : PROT)
                -> Capable (DPair (Global Nil    rs)
                              (Global Nil ts rs))
  synth types roles p
    = synth Nil types roles (toProtocol p)

-- [ EOF ]
