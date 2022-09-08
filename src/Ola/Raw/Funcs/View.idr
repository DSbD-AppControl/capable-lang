||| Turn the abstract AST to something more precise.
|||
||| Module    : Ola.Raw.Funcs.View
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
module Ola.Raw.Funcs.View

import Toolkit.Data.Location
import Toolkit.Data.DList

import Ola.Types
import Ola.Raw.Types
import Ola.Raw.Types.View

import Ola.Raw.Exprs
import Ola.Raw.Exprs.View

import Ola.Raw.Stmts
import Ola.Raw.Stmts.View

import Ola.Raw.Funcs

%default total

public export
data Args : List (FileContext, Ref, Raw.Ty) -> Type where
  Empty : Args Nil
  Extend : (fc : FileContext)
        -> (ref : Ref)
        -> (ty  : Ty t)
        -> (rest : Args as)
                -> Args ((fc,ref,t)::as)

public export
data Func : (s : Raw.Func) -> Type where
  F : (fc  : FileContext)
   -> (aTy : Args argTy)
   -> (rTy : Ty reTy)
   -> (body : Stmt scope)
   -> (last : Expr r)
         -> Func (Null fc (FUNC argTy reTy scope r))


viewArgs : (as : List (FileContext, Ref, Raw.Ty))
              -> Args as
viewArgs [] = Empty
viewArgs ((fc,ref,ty) :: xs)
  = Extend fc ref (view ty) (viewArgs xs)

export
view : (s : Raw.Func) -> Func s
view (Null fc (FUNC as r b e))
  = F fc (viewArgs as) (view r) (view b) (view e)


export
getFC : {s : Func} -> Func s -> FileContext
getFC {s} _ = getFC s

-- [ EOF ]
