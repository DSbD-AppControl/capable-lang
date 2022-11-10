||| Type-checker for bidirectional typed Syntax for types.
|||
||| Module    : Types.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
module Ola.Check.Types

import Toolkit.Data.Location
import Toolkit.Data.DList

import Data.Singleton

import Ola.Types
import Ola.Core

import Ola.Raw.AST
import Ola.Raw.Types

import Ola.Check.Common

import Ola.Terms.Vars
import Ola.Terms.Types

%default total


mutual

  synthArgs : {types : List Ty.Base}
           -> (ctxt  : Context Ty.Base types)
           -> (args  : Args as)
                    -> Ola (DPair (List Ty.Base)
                                  (DList Ty.Base (Ty types)))
  synthArgs ctxt []
    = pure (_ ** Nil)

  synthArgs ctxt (ty :: rest)
    = do (a  ** ty)  <- synth ctxt ty
         (as ** tys) <- synthArgs ctxt rest
         pure (_ ** ty :: tys)

  export
  synth : {types : List Ty.Base}
       -> (ctxt : Context Ty.Base types)
       -> (syn  : Ty t)
               -> Ola (DPair Ty.Base (Ty types))

  synth ctxt (TyVar x prf)
    = do (ty ** idx) <- lookup ctxt x
         pure (_ ** TyVar idx)

  synth ctxt (TyChar fc)
    = pure (_ ** TyChar)

  synth ctxt (TyStr fc)
    = pure (_ ** TyStr)

  synth ctxt (TyInt fc)
    = pure (_ ** TyInt)

  synth ctxt (TyBool fc)
    = pure (_ ** TyBool)

  synth ctxt (TyUnit fc)
    = pure (_ ** TyUnit)

  synth ctxt (TyArray fc n ty)
    = do (ty ** tm) <- synth ctxt ty
         ifThenElse (n < 0)
                    (throwAt fc NatExpected)
                    (pure (_ ** TyArray tm (cast n)))

  synth ctxt (TyPair fc f s)
    = do (tyF ** tmF) <- synth ctxt f
         (tyS ** tmS) <- synth ctxt s

         pure (_ ** TyPair tmF tmS)

  synth ctxt (TyUnion fc l r)
    = do (tyF ** tmF) <- synth ctxt l
         (tyS ** tmS) <- synth ctxt r

         pure (_ ** TyUnion tmF tmS)

  synth ctxt (TyRef fc ty)
    = do (ty ** tm) <- synth ctxt ty
         pure (_ ** TyRef tm)

  synth ctxt (TyHandle fc k)
    = pure (_ ** TyHandle k)

  synth ctxt (TyFunc fc prf args retty)
    = do (tyAS ** args) <- synthArgs ctxt args
         (tyR  ** ret)  <- synth     ctxt retty
         pure (_ ** TyFunc args ret)

namespace Raw
  export
  synth : {types : List Ty.Base}
       -> (ctxt  : Context Ty.Base types)
       -> (raw   : TYPE)
                -> Ola (DPair Ty.Base (Ty types))
  synth ctxt r
    = synth ctxt (toType r)

-- ## Reflect

mutual
  reflectArgs : {types : List Ty.Base}
             -> (delta : Context Ty.Base types)
             -> (ts    : List Ty.Base)
                      -> Ola (DList Ty.Base (Ty types) ts)
  reflectArgs delta []
    = pure Nil

  reflectArgs delta (x :: xs)
    = pure $ (::) !(reflect     delta x)
                  !(reflectArgs delta xs)

  export
  reflect : {types : List Ty.Base}
         -> (delta : Context Ty.Base types)
         -> (type  : Ty.Base)
                  -> Ola (Ty types type)

  reflect delta CHAR
    = pure TyChar
  reflect delta STR
    = pure TyStr
  reflect delta INT
    = pure TyInt
  reflect delta BOOL
    = pure TyBool
  reflect delta (ARRAY x k)
    = pure (TyArray !(reflect delta x) k)
  reflect delta (PAIR x y)
    = pure (TyPair !(reflect delta x)
                   !(reflect delta y))

  reflect delta (UNION x y)
    = pure (TyUnion !(reflect delta x)
                    !(reflect delta y))

  reflect delta UNIT
    = pure TyUnit

  reflect delta (REF x)
    = pure (TyRef !(reflect delta x))

  reflect delta (HANDLE x)
    = pure (TyHandle x)
  reflect delta (FUNC xs x)
    = pure (TyFunc !(reflectArgs delta xs)
                   !(reflect     delta x))

-- [ EOF ]
