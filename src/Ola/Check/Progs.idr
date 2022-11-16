||| Type-checker for Programs.
|||
||| Module    : Types.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
module Ola.Check.Progs

import Data.List.Views
import Data.String

import Toolkit.Data.Location

import Ola.Types
import Ola.Core

import Ola.Raw.AST
import Ola.Raw.Types
import Ola.Raw.Exprs

import Ola.Raw.Funcs
import Ola.Raw.Role
import Ola.Raw.Progs
import Ola.Check.Common

import Ola.Check.Types
import Ola.Check.Roles
import Ola.Check.Protocols
import Ola.Check.Exprs
import Ola.Check.Funcs

import Ola.Terms.Vars
import Ola.Terms.Roles
import Ola.Terms.Protocols
import Ola.Terms.Types
import Ola.Terms.Exprs
import Ola.Terms.Funcs
import Ola.Terms.Progs

import Ola.REPL.State

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

generateProjections : {t,fields,p : _ } -> Ty t -> Named.Args fields -> Prog p -> DPair PROG Prog
generateProjections rtype fs scope
  = let gs = projs projGet rtype fs in
    let ss = projs projSet rtype fs
    in foldr foldFun (_ ** scope) (gs ++ ss)

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
     -> {ds,gs : List Ty.Base}
     -> (env   : Env rs ds gs)
     -> (state : State)
     -> (prog  : Prog p)
              -> Ola (Prog rs ds gs UNIT, State)
check env state (Main fc m)
  = do (tyM ** m) <- synth env m

       Refl <- compare fc (FUNC Nil UNIT) tyM

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

check env state (Def fc TYPE n val@(TyData fc' STRUCT _ args) scope)
  = do exists fc (delta env) n
       (ty ** tm) <- synth (delta env) val

       let (p ** scope) = generateProjections val args scope

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

       tyTm <- reflect (delta env) (FUNC as r)

       pure (DefFunc tyTm tm scope, state)

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

       let state = {protocols $= insert n (P (rho env) tm)} state

       (scope, state) <- check env state scope

       pure (DefSesh tm scope, state)


namespace Raw
  export
  check : (r : PROG) -> Ola (Program,State)
  check p
    = check empty defaultState (toProg p)



-- [ EOF ]
