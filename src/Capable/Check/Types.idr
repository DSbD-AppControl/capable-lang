||| Type-checker for bidirectional typed Syntax for types.
|||
||| Module    : Types.idr
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Capable.Check.Types

import Toolkit.Data.Location
import Toolkit.Data.DList
import Toolkit.Data.DVect

import Data.Singleton

import Capable.Types
import Capable.Core

import Capable.Raw.AST
import Capable.Raw.Types

import Capable.Check.Common

import Capable.Terms.Vars
import Capable.Terms.Types

%default total
%hide type

mutual

  synthArgs : {types : List Ty.Base}
           -> (ctxt  : Context Ty.Base types)
           -> (args  : Types.Args as)
                    -> Capable (DPair (List Ty.Base)
                                  (DList Ty.Base (Ty types)))
  synthArgs ctxt []
    = pure (_ ** Nil)

  synthArgs ctxt (ty :: rest)
    = do (a  ** ty)  <- synth ctxt ty
         (as ** tys) <- synthArgs ctxt rest
         pure (_ ** ty :: tys)

  synthArgs' : {types : List Ty.Base}
           -> (ctxt  : Context Ty.Base types)
           -> (args  : Types.Args as)
                    -> Capable (DPair Nat
                                  (\n => DPair (Vect n Ty.Base)
                                  (DVect Ty.Base (Ty types) n)))
  synthArgs' ctxt []
    = pure (_ ** _ ** Nil)

  synthArgs' ctxt (ty :: rest)
    = do (a  ** ty)  <- synth ctxt ty
         (_ ** as ** tys) <- synthArgs' ctxt rest
         pure (_ ** _ ** ty :: tys)

  export
  synth : {types : List Ty.Base}
       -> (ctxt : Context Ty.Base types)
       -> (syn  : Ty t)
               -> Capable (DPair Ty.Base (Ty types))

  synth ctxt (TyVar x prf)
    = do (ty ** idx) <- lookup ctxt x
         pure (ty ** TyVar idx)

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

  synth ctxt (TyList fc ty)
    = do (ty ** tm) <- synth ctxt ty
         pure (_ ** TyList tm)

  synth ctxt (TyVector fc n ty)
    = do (ty ** tm) <- synth ctxt ty
         ifThenElse (n < 0)
                    (throwAt fc NatExpected)
                    (pure (_ ** TyVector tm (cast n)))

  synth ctxt (TyTuple fc prf (a::b::fs))
    = do (_ ** _ ** (a :: b :: args)) <- synthArgs' ctxt (a::b::fs)
               | _ => throwAt fc Unknown
         pure (_ ** TyTuple (a::b::args))

  synth ctxt (TyRef fc ty)
    = do (ty ** tm) <- synth ctxt ty
         pure (_ ** TyRef tm)

  synth ctxt (TyHandle fc k)
    = pure (_ ** TyHandle k)

namespace Raw
  export
  synth : {types : List Ty.Base}
       -> (ctxt  : Context Ty.Base types)
       -> (raw   : TYPE)
                -> Capable (DPair Ty.Base (Ty types))
  synth ctxt r
    = synth ctxt (toType r)

-- ## Reflect

mutual
  reflectFields : {types : List Ty.Base}
               -> (delta : Context Ty.Base types)
               -> (ts    : List1 (String, Ty.Base))
                        -> Capable (DList (String, Base)
                                      (Ty types . Builtin.snd)
                                      (forget ts))
  reflectFields delta ((x, y) ::: [])
    = do x' <- reflect delta y
         pure (x'::Nil)

  reflectFields delta ((x, y) ::: (z :: xs))
    = do y' <- reflect delta y
         rest <- assert_total $ reflectFields delta (z:::xs)

         pure $ (::) (y') rest


  reflectArgs' : {types : List Ty.Base}
             -> (delta : Context Ty.Base types)
             -> (ts    : Vect n Ty.Base)
                      -> Capable (DVect Ty.Base (Ty types) n ts)
  reflectArgs' delta []
    = pure Nil
  reflectArgs' delta (x :: xs)
    = pure $ (::) !(reflect delta x)
                  !(reflectArgs' delta xs)


  reflectArgs : {types : List Ty.Base}
             -> (delta : Context Ty.Base types)
             -> (ts    : List Ty.Base)
                      -> Capable (DList Ty.Base (Ty types) ts)
  reflectArgs delta []
    = pure Nil

  reflectArgs delta (x :: xs)
    = pure $ (::) !(reflect     delta x)
                  !(reflectArgs delta xs)

  export
  reflect : {types : List Ty.Base}
         -> (delta : Context Ty.Base types)
         -> (type  : Ty.Base)
                  -> Capable (Ty types type)

  reflect delta CHAR
    = pure TyChar
  reflect delta STR
    = pure TyStr
  reflect delta INT
    = pure TyInt
  reflect delta BOOL
    = pure TyBool

  reflect delta (LIST x)
    = pure (TyList !(reflect delta x))

  reflect delta (VECTOR x k)
    = pure (TyVector !(reflect delta x) k)

  reflect delta (TUPLE xs)
    = pure (TyTuple !(reflectArgs' delta xs))


  reflect delta (UNION (f:::fs))
    = pure (TyUnion !(reflectFields delta (f:::fs)))

  reflect delta (RECORD (f:::fs))
    = pure (TyRecord !(reflectFields delta (f:::fs)))

  reflect delta UNIT
    = pure TyUnit

  reflect delta (REF x)
    = pure (TyRef !(reflect delta x))

  reflect delta (HANDLE x)
    = pure (TyHandle x)

-- [ EOF ]
