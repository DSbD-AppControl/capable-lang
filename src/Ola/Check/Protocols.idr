||| Type-checker for protocols.
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Ola.Check.Protocols

import Toolkit.Data.Location
import Toolkit.Data.DList
import Toolkit.Data.List.AtIndex

import Data.Singleton

import Ola.Types
import Ola.Core


import Ola.Raw.AST
import Ola.Raw.Role
import Ola.Raw.Types
import Ola.Raw.Exprs
import Ola.Raw.Protocols

import Ola.Check.Common
import Ola.Check.Types
import Ola.Check.Roles

import Ola.Terms.Vars
import Ola.Terms.Roles
import Ola.Terms.Types
import Ola.Terms.Protocols

%default total

mutual
  branch : {ts    : List Base}
        -> {rs    : List Ty.Role}
        -> {ks    : List Protocol.Kind}
        -> (kinds : Context Protocol.Kind    ks)
        -> (types : Context Ty.Base ts)
        -> (roles : Context Ty.Role rs)
        -> (bs1   : Branch b)
                 -> Ola (DPair (Global.Branch ks    rs)
                               (Branch        ks ts rs))
  branch kinds types roles (B fc label type cont)
    = do (t ** type) <- synth types type
         (g ** cont) <- synth kinds types roles cont

         pure (_ ** B label type cont)

  branches : {ts    : List Base}
          -> {rs    : List Ty.Role}
          -> {ks    : List Protocol.Kind}
          -> (kinds : Context Protocol.Kind    ks)
          -> (types : Context Ty.Base ts)
          -> (roles : Context Ty.Role rs)
          -> (bs1   : All Branch bs)
                   -> Ola (DPair (Global.Branches ks    rs)
                                 (Branches        ks ts rs))
  branches kinds types roles []
    = pure (_ ** Nil)
  branches kinds types roles (x :: y)
    = do (tyB  ** b)  <- branch   kinds types roles x
         (tyBS ** bs) <- branches kinds types roles y

         pure (_ ** b::bs)


  synth : {ts : List Base}
       -> {ks : List Protocol.Kind}
       -> {rs : List Ty.Role}
       -> (kinds : Context Protocol.Kind    ks)
       -> (types : Context Ty.Base ts)
       -> (roles : Context Ty.Role rs)
       -> (syn   : Protocol g)
                -> Ola (DPair (Ty.Global ks    rs)
                              (Global    ks ts rs))
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

  synth kinds types roles (Choice fc s r prf (B1 (x::xs)))
    = do (MkRole ** stm) <- synth roles s
         (MkRole ** rtm) <- synth roles r

         (tyB  ** tmB)  <- branch kinds types roles x
         (tyBs ** tmBs) <- branches kinds types roles xs

         case Index.decEq stm rtm of
           Yes (Same Refl Refl)
             => do let R s' = s
                   let R r' = r
                   throwAt fc (MismatchRole (MkRef emptyFC s') (MkRef emptyFC r'))
           No prf
             => pure (_ ** Choice stm rtm prf (Bs1 (tmB::tmBs)))

namespace View
  export
  synth : {ts : List Base}
       -> {rs : List Ty.Role}
       -> (types : Context Ty.Base ts)
       -> (roles : Context Ty.Role rs)
       -> (syn   : Protocol g)
                -> Ola (DPair (Ty.Global Nil    rs)
                              (Global    Nil ts rs))
  synth types roles p
    = synth Nil types roles p

namespace Raw

  export
  synth : {ts    : List Ty.Base}
       -> {rs    : List Ty.Role}
       -> (types : Context Ty.Base ts)
       -> (roles : Context Ty.Role rs)
       -> (sesh  : PROT)
                -> Ola (DPair (Ty.Global Nil    rs)
                                 (Global Nil ts rs))
  synth types roles p
    = synth Nil types roles (toProtocol p)

-- [ EOF ]
