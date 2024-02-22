||| Type-checker for funcs.
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Capable.Check.Funcs

import Toolkit.Data.Location

import Capable.Types
import Capable.Core

import Capable.Raw.AST
import Capable.Raw.Types
import Capable.Raw.Exprs
import Capable.Raw.Funcs


import Capable.Check.Common

import Capable.Check.Types
import Capable.Check.Exprs

import Capable.Terms.Vars
import Capable.Terms.Types
import Capable.Terms.Exprs
import Capable.Terms.Funcs

import Capable.State

%default total

export
data Instrs : (delta : List Ty.Base)
           -> (args  : Vect.Quantifiers.All.All Arg as)
           -> (tys   : List Ty.Base)
                    -> Type
  where
    Empty : Instrs d Nil Nil
    Arg : {0 ty' : Ty a}
       -> {  as : Vect.Quantifiers.All.All Arg xs}
       -> (s   : String)
       -> (ty  : Ty.Base)
       -> (tm  : Ty d ty)
       -> (rest : Instrs d                as         tys)
               -> Instrs d (A fc s ty' :: as) (ty :: tys)

export
args : {ds    : List Ty.Base}
    -> (delta : Context Ty.Base ds)
    -> {as    : Vect n ARG}
    -> (args  : All Arg as)
             -> Capable (DPair (List Ty.Base)
                            (Instrs ds args))
args  delta []
  = pure ((_ ** Empty))

args delta (A fc ref ty :: y)
  = do (ty ** tm) <- synth delta ty
       (_ ** rest) <- args delta y
       pure (_ ** Arg ref ty tm rest)

export
expand : {as' : Vect.Quantifiers.All.All Arg as''}
      -> (is  : Instrs ds as' as)
               -> Context Ty.Base as
expand Empty
  = Nil
expand (Arg ref ty tm rest)
  = extend (expand rest) ref ty


export
synth : {f    : FUNC}
     -> {rs   : List Ty.Role}
     -> {ds   : List Ty.Base}
     -> {gs   : List Ty.Method}
     -> {ss   : List Ty.Session}
     -> State
     -> (rho  : Env rs ds ss gs Nil)
     -> (func : Fun f)
             -> Capable (State, DPair Ty.Method (Func rs ds ss gs))
synth st env (Func fc prf as ret scope)
  = do (tyAS  ** as)  <- args  (delta env) as
       (tyRet ** ret) <- synth (delta env) ret

--       (st, (tyScope ** scope)) <- synth st ({lambda := expand as} env) scope
       (st, T _ scope) <- Exprs.check st fc ({lambda := expand as} env) ret scope
--       Refl <- compare fc tyRet tyScope
       pure (st, (FUNC tyAS tyRet ** Fun scope))


namespace Raw
  export
  synth : {rs  : List Ty.Role}
       -> {ds  : List Ty.Base}
       -> {gs  : List Ty.Method}
       -> {ss  : List Ty.Session}
       -> State
       -> (env : Env rs ds ss gs Nil)
       -> (syn : FUNC)
              -> Capable (State, DPair Ty.Method (Func rs ds ss gs))
  synth st env f
    = synth st env (toFun f)


-- [ EOF ]
