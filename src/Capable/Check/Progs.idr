||| Type-checker for Programs.
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Capable.Check.Progs

import Data.List.Views
import Data.String

import Toolkit.Data.Location

import Capable.Types
import Capable.Core

import Capable.Raw.AST
import Capable.Raw.Types
import Capable.Raw.Exprs

import Capable.Raw.Funcs
import Capable.Raw.Role
import Capable.Raw.Progs
import Capable.Check.Common

import Capable.Check.Types
import Capable.Check.Roles
import Capable.Check.Protocols
import Capable.Check.Exprs
import Capable.Check.Funcs
import Capable.Check.Sessions

import Capable.Terms.Vars
import Capable.Terms.Roles
import Capable.Terms.Protocols
import Capable.Terms.Sessions
import Capable.Terms.Types
import Capable.Terms.Exprs
import Capable.Terms.Funcs
import Capable.Terms.Progs

import Capable.State

%default total
%hide fields

-- # First we elaboration some functions for projecting records
projGet : {t,t' : _}
       -> FileContext
       -> Ty t
       -> String
       -> Ty t'
       -> (DPair FUNC (\f => (FileContext, String, Fun f)))
projGet fc atype str rtype
  = (_ ** ( fc
          , "get_" ++ str
          , Func {fc' = fc}
               fc
               (Next Empty)
               [A fc "label" atype]
               rtype
               (GetR fc str (Var (MkRef fc "label") R))))

projSet : {t,t' : _}
       -> FileContext
       -> Ty t
       -> String
       -> Ty t'
       -> (DPair FUNC (\f => (FileContext, String, Fun f)))
projSet fc atype str rtype
  = (_ ** ( fc
          , "set_" ++ str
          , Func {fc' = fc}
               fc
               (Next (Next Empty))
               [A fc "rec" atype, A fc "val" rtype ]
               atype
               (SetR fc
                     str
                     (Var (MkRef fc "rec") R)
                     (Var (MkRef fc "val") R))))

data PArgs : Vect n FIELD -> Type where
  PA : {fs : Vect n FIELD}
    -> {as : _}
    -> {vs : Vect n ARG}
    -> (prf : AsVect as vs)
    -> (val : All Arg vs)
           -> PArgs fs

projArgs : {f : _}
        -> {fields : Vect n FIELD}
        -> Named.Args (f::fields)
        -> PArgs (f::fields)

projArgs (Add fc s ty Nil)
  = PA (Next Empty)
       ((A fc s ty ) :: All.Nil)

projArgs (Add fc s ty (Add fc' s' ty' rest))
  = let (PA prf tms) = projArgs (Add fc' s' ty' rest)
    in PA (Next prf)
          (A fc s ty :: tms)

data PRefs : Vect n FIELD -> Type where
  PR : {fs : Vect n FIELD}
    -> {as : _}
    -> {vs : Vect n FIELDV}
    -> (prf : AsVect as vs)
    -> (val : All Field vs)
           -> PRefs fs

projRefs : {f : _}
        -> {fields : Vect n FIELD}
        -> Named.Args (f :: fields)
        -> PRefs (f::fields)

projRefs (Add fc s ty Nil)
  = PR (Next Empty)
       ((F fc s (Var (MkRef fc s) R) ):: All.Nil)

projRefs (Add fc s _ (Add fc' s' ty' rest))
  = let PR prf tms = projRefs (Add fc' s' ty' rest)
    in  PR (Next prf)
           (F fc s (Var (MkRef fc s) R) :: tms)

projCtor : {t, f,fields' : _}
        -> FileContext
        -> String
        -> Ty t
        -> Named.Args (f::fields')
        -> (DPair FUNC (\f => (FileContext, String, Fun f)))
projCtor fc n rtype argso
   = let PA pa args = projArgs argso in
     let PR pr refs = projRefs argso
     in (_ ** ( fc
              , n
              , Func {fc' = fc}
                   fc
                   pa
                   args
                   rtype
                   (Record fc pr (refs))
               ))

projs : {t, fields' : _}
     -> (f : {t,t' : _}
          -> FileContext
          -> Ty t
          -> String
          -> Ty t'
          -> (DPair FUNC (\f => (FileContext, String, Fun f))))
     -> Ty t
     -> Named.Args fields'
     -> List (DPair FUNC (\f => (FileContext, String, Fun f)))
projs f atype Nil = Nil
projs f atype (Add fc' s t xs)
  = f fc' atype s t :: projs f atype xs

foldFun : (DPair FUNC (\f => (FileContext, String, Fun f)))
        -> DPair PROG Prog
        -> DPair PROG Prog
foldFun (f' ** (fc,label,fn)) (p' ** scope)
  = (_ ** Def fc FUNC label fn scope)

generateProjections : {t,f,fields,p : _ }
                   -> FileContext
                   -> String
                   -> Ty t
                   -> Named.Args (f::fields)
                   -> Prog p
                   -> DPair PROG Prog
generateProjections fc n rtype fs scope
  = let gs = projs projGet rtype fs in
    let ss = projs projSet rtype fs in
    let ctor = projCtor fc n rtype fs
    in foldr foldFun (_ ** scope) (ctor :: gs ++ ss)

-- # We do the same for unions
projTag : {t,t' : _}
       -> FileContext
       -> Ty t
       -> String
       -> Ty t'
       -> (DPair FUNC (\f => (FileContext, String, Fun f)))
projTag fc atype str rtype
  = (_ ** ( fc
          , str
          , Func {fc' = fc}
               fc
               (Next Empty)
               [A fc "value" rtype]
               atype
               (The fc atype (Tag fc str (Var (MkRef fc "value") R)))

               ))

generateTags : {t,fields,p : _ } -> Ty t -> Named.Args fields -> Prog p -> DPair PROG Prog
generateTags rtype fs scope
  = let gs = projs projTag rtype fs
    in foldr foldFun (_ ** scope) gs

check : {p     : PROG}
     -> {rs    : List Ty.Role}
     -> {ds    : List Ty.Base}
     -> {gs    : List Ty.Method}
     -> {ss    : List Ty.Session}
     -> (env   : Env rs ds ss gs Nil)
     -> (state : State)
     -> (prog  : Prog p)
              -> Capable (Prog rs ds ss gs UNIT, State)
check env state (Main fc m)
  = do (FUNC Nil UNIT ** m) <- synth env m
         | (ty ** _)
             => throwAt fc (MismatchM ty (FUNC Nil UNIT))

       pure (Main m, state)

-- [ NOTE ]
--
-- The following should be cleaner, but we have reached the limit of
-- Idris2 inference abilities to reconstruct the raw ast from the
-- projections.
--
-- Well maybe gallais can get it working, but I cannot...
check env state (Def fc TYPE n val@(TyData fc' UNION _ args) scope)
  = do exists fc (delta env) n
       (ty ** tm) <- synth (delta env) val

       let (p ** scope) = generateTags val args scope

       let env   = { delta $= \c => extend c n ty} env
       let state = { types $= insert n (T tm)} state

       (scope, state) <- assert_total $ check env state scope

       pure (DefType tm scope, state)

check env state (Def fc TYPE n val@(TyData fc' STRUCT _ (Add a b c d)) scope)
  = do exists fc (delta env) n
       (ty ** tm) <- synth (delta env) val

       let (p ** scope) = generateProjections fc n val (Add a b c d) scope

       let env   = { delta $= \c => extend c n ty} env
       let state = { types $= insert n (T tm)} state

       (scope, state) <- assert_total $ check env state scope

       pure (DefType tm scope, state)

check env state (Def fc TYPE n val {rest} scope)
  = do exists fc (delta env) n
       (ty ** tm) <- synth (delta env) val

       let env   = { delta $= \c => extend c n ty} env
       let state = { types $= insert n (T tm)} state

       (scope, state) <- check env state scope

       pure (DefType tm scope, state)

check env state (Def fc FUNC n val scope)
  = do exists fc (gamma env) n

       (FUNC as r ** tm) <- synth env val
         | (ty ** _) => throwAt fc (FunctionExpected ty)

       let env   = Gamma.extend env n (FUNC as r)
       let state = { funcs $= insert n (F tm)} state

       (scope, state) <- check env state scope

       pure (DefFunc tm scope, state)

check env state (Def fc ROLE n val scope)

  = do exists fc (rho env) n
       let env = extend env n

       (MkRole ** role) <- synth (rho env) val

       let state = {roles $= insert n (MkRole)} state

       (scope, state) <- check env state scope

       pure (DefRole scope, state)


check env state (Def fc PROT n val scope)
  = do maybe (pure ())
             (\_ => throwAt fc (AlreadyBound (MkRef fc n )))
             (!(getProtocol state n))

       (g ** tm) <- synth (delta env) (rho env) val

       let env = Sigma.extend env n (S (rho env) g)

       let state = {protocols $= insert n (P (rho env) tm)} state

       (scope, state) <- check env state scope

       pure (DefProt tm  scope, state)

check env state (Def fc SESH n val scope)
  = do exists fc (gamma env) n

       (SESH ctzt whom l as r ** tm) <- synth env val
         | (ty ** _) => throwAt fc (SessionExpected ty)

       let env = Gamma.extend env n (SESH ctzt whom l as r)
       -- @ TODO add sessions to state

       (scope, state) <- check env state scope
       pure (DefSesh tm scope, state)

namespace Raw
  export
  check : (r : PROG) -> Capable (Program,State)
  check p
    = check empty defaultState (toProg p)



-- [ EOF ]
