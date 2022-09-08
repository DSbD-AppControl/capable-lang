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

import Ola.Raw.Types
import Ola.Raw.Types.View
import Ola.Raw.Exprs

import Ola.Raw.Stmts
import Ola.Raw.Funcs
import Ola.Raw.Funcs.View

import Ola.Check.Common

import Ola.Check.Types
import Ola.Check.Exprs
import Ola.Check.Stmts

import Ola.Terms.Vars
import Ola.Terms.Types
import Ola.Terms.Exprs
import Ola.Terms.Stmts
import Ola.Terms.Funcs

%default total

data Instrs : (delta : List Types.Ty)
           -> (args  : Funcs.View.Args as)
           -> (tys   : List Types.Ty)
                    -> Type
  where
    Empty : Instrs delta Empty Nil
    Arg : (ref : Ref)
       -> (ty  : Types.Ty)
       -> (tm  : Ty delta ty)
       -> (rest : Instrs delta as tys)
               -> Instrs delta (Extend fc ref ty' as) (ty :: tys)


checkArgs : {ds    : List Types.Ty}
         -> (delta : Context Types.Ty ds)
         -> {as    : List (FileContext,Ref,Raw.Ty)}
         -> (args  : Args as)
                  -> Ola (DPair (List Types.Ty)
                                (Instrs ds args))
checkArgs delta Empty
  = pure (_ ** Empty)
checkArgs delta (Extend fc ref ty rest)
  = do (ty ** tm) <- typeCheck delta ty
       (_ ** rest) <- checkArgs delta rest
       pure (_ ** Arg ref ty tm rest)

expand : (gamma : Context Types.Ty gs)
      -> (is    : Instrs ds args as)
               -> Context Types.Ty (as ++ gs)
expand gamma Empty
  = gamma
expand gamma (Arg ref ty tm rest)
  = extend (expand gamma rest) (get ref) ty

check : {f     : Func}
     -> {ds,gs : List Types.Ty}
     -> (delta : Context Types.Ty ds)
     -> (gamma : Context Types.Ty gs)
     -> (func  : Func f)
              -> Ola (DPair Types.Ty (Func ds gs))

check delta gamma (F fc aTy rTy body last)
  = do (tyAs ** as) <- checkArgs delta aTy
       (rty ** rtm) <- typeCheck delta rTy

       R newG rTy' body Refl <- stmtCheck
                                  delta
                                  (expand gamma as)
                                  rty
                                  body
       (ty ** last) <- exprCheck
                         delta
                         newG
                         last

       Refl <- compare fc ty rTy'

       pure (FUNC tyAs rTy' ** Fun body last)

export
funcCheck : {r     : Func}
         -> {ds,gs : List Types.Ty}
         -> (delta : Context Types.Ty ds)
         -> (gamma : Context Types.Ty gs)
         -> (syn   : Func r)
                  -> Ola (DPair Types.Ty (Func ds gs))

funcCheck
  = check

namespace Raw
  export
  funcCheck : {ds,gs : List Types.Ty}
           -> (delta : Context Types.Ty ds)
           -> (gamma : Context Types.Ty gs)
           -> (syn   : Func)
                   -> Ola (DPair Types.Ty (Func ds gs))
  funcCheck d g e
    = check d g (view e)
-- [ EOF ]
