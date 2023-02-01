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

%default total


data Instrs : (delta : List Ty.Base)
           -> (args  : All Arg as)
           -> (tys   : List Ty.Base)
                    -> Type
  where
    Empty : Instrs d Nil Nil
    Arg : {0 ty' : Ty a}
       -> {  as : All Arg xs}
       -> (s   : String)
       -> (ty  : Ty.Base)
       -> (tm  : Ty d ty)
       -> (rest : Instrs d                as         tys)
               -> Instrs d (A fc s ty' :: as) (ty :: tys)

args : {ds    : List Ty.Base}
    -> (delta : Context Ty.Base ds)
    -> {as    : Vect n ARG}
    -> (args  : All Arg as)
             -> Capable (DPair (List Ty.Base)
                            (Instrs ds args))
args delta []
  = pure (_ ** Empty)

args delta (A fc ref ty :: y)
  = do (ty ** tm) <- synth delta ty
       (_ ** rest) <- args delta y
       pure (_ ** Arg ref ty tm rest)


expand : {as' : All Arg as''}
      -> (is    : Instrs ds as' as)
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
     -> (rho  : Env rs ds ss gs Nil)
     -> (func : Fun f)
             -> Capable (DPair Ty.Method (Func rs ds ss gs))
synth env (Func fc prf as ret scope)
  = do (tyAS  ** as)  <- args  (delta env) as
       (tyRet ** ret) <- synth (delta env) ret

       (tyScope ** scope) <- synth ({lambda := expand as} env) scope

       Refl <- compare fc tyRet tyScope
       pure (FUNC tyAS tyRet ** Fun scope)


namespace Raw
  export
  synth : {rs  : List Ty.Role}
       -> {ds  : List Ty.Base}
       -> {gs  : List Ty.Method}
       -> {ss  : List Ty.Session}
       -> (env : Env rs ds ss gs Nil)
       -> (syn : FUNC)
              -> Capable (DPair Ty.Method (Func rs ds ss gs))
  synth env f
    = synth env (toFun f)


-- [ EOF ]
