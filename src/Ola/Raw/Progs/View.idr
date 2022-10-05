||| Turn the abstract AST to something more precise.
|||
||| Module    : Ola.Raw.Progs.View
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
module Ola.Raw.Progs.View

import Toolkit.Data.Location
import Toolkit.Data.DList

import Ola.Types

import Ola.Raw.Roles

import Ola.Raw.Types
import Ola.Raw.Types.View

import Ola.Raw.Sessions
import Ola.Raw.Sessions.View

import Ola.Raw.Exprs
import Ola.Raw.Exprs.View

import Ola.Raw.Stmts
import Ola.Raw.Stmts.View

import Ola.Raw.Funcs
import Ola.Raw.Funcs.View

import Ola.Raw.Progs

%default total

public export
data Prog : (s : Raw.Prog) -> Type where
  RoleDefSyn : (fc    : FileContext)
            -> (ref   : Ref)
            -> (role  : Raw.Role)
            -> (scope : Prog body)
                     -> Prog (Un fc (DEFROLESYN ref role) body)

  RoleDef : (fc    : FileContext)
         -> (ref   : Ref)
         -> (scope : Prog body)
                  -> Prog (Un fc (DEFROLE ref) body)

  TypeDef : (fc    : FileContext)
         -> (ref   : Ref)
         -> (val   : Ty t)
         -> (scope : Prog body)
                  -> Prog (Un fc (DEFTYPE ref t) body)

  SeshDef : (fc    : FileContext)
         -> (ref   : Ref)
         -> (sesh  : Sessions s)
         -> (scope : Prog body)
                  -> Prog (Un fc (DEFSESH ref s) body)

  FuncDef : (fc    : FileContext)
         -> (ref   : Ref)
         -> (val   : Func f)
         -> (scope : Prog body)
                  -> Prog (Un fc (DEFFUNC ref f) body)
  Main : (fc : FileContext)
      -> (body : Func f)
              -> Prog (Null fc (MAIN f))

export
view : (s : Raw.Prog) -> Prog s
view (Null fc (MAIN f))
  = Main fc (view f)

view (Un fc (DEFTYPE x y) rem)
  = TypeDef fc x (view y) (view rem)

view (Un fc (DEFFUNC x y) rem)
  = FuncDef fc x (view y) (view rem)

view (Un fc (DEFROLE x) rem)
  = RoleDef fc x (view rem)

view (Un fc (DEFROLESYN x y) rem)
  = RoleDefSyn fc x y (view rem)

view (Un fc (DEFSESH ref s) rem)
  = SeshDef fc ref (view s) (view rem)

export
getFC : {s : Prog} -> Prog s -> FileContext
getFC {s} _ = getFC s

-- [ EOF ]
