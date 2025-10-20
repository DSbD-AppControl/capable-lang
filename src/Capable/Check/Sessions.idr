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

import Capable.Check.Sessions.Expr.Check
import Capable.Check.Sessions.Expr.Synth

%hide Capable.State.State.roles

%default total

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
