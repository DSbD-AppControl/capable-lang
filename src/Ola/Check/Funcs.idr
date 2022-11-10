||| Type-checker for funcs.
|||
||| Module    : Types.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
module Ola.Check.Funcs

import Toolkit.Data.Location

import Ola.Types
import Ola.Core

import Ola.Raw.AST
import Ola.Raw.Types
import Ola.Raw.Exprs
import Ola.Raw.Funcs


import Ola.Check.Common

import Ola.Check.Types
import Ola.Check.Exprs

import Ola.Terms.Vars
import Ola.Terms.Types
import Ola.Terms.Exprs
import Ola.Terms.Funcs

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
             -> Ola (DPair (List Ty.Base)
                            (Instrs ds args))
args delta []
  = pure (_ ** Empty)

args delta (A fc ref ty :: y)
  = do (ty ** tm) <- synth delta ty
       (_ ** rest) <- args delta y
       pure (_ ** Arg ref ty tm rest)


expand : {as' : All Arg as''}
      -> (is    : Instrs ds as' as)
      -> (gamma : Context Ty.Base gs)
               -> Context Ty.Base (as ++ gs)
expand Empty gamma
  = gamma
expand (Arg ref ty tm rest) gamma
  = extend (expand rest gamma) ref ty


export
synth : {f     : FUNC}
     -> {rs    : List Ty.Role}
     -> {ds,gs : List Ty.Base}
     -> (rho   : Env rs ds gs)
     -> (func  : Fun f)
              -> Ola (DPair Ty.Base (Func rs ds gs))
synth env (Func fc prf as ret scope)
  = do (tyAS  ** as)  <- args  (delta env) as
       (tyRet ** ret) <- synth (delta env) ret

       (tyScope ** scope) <- synth ({gamma $= expand as} env) scope

       Refl <- compare fc tyRet tyScope
       pure (FUNC tyAS tyRet ** Fun scope)


namespace Raw
  export
  synth : {rs    : List Ty.Role}
       -> {ds,gs : List Ty.Base}
       -> (env   : Env rs ds gs)
       -> (syn   : FUNC)
              -> Ola (DPair Ty.Base (Func rs ds gs))
  synth env f
    = synth env (toFun f)


-- [ EOF ]
