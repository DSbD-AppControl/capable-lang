||| Views on types.
|||
||| Module    : Types.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
|||
||| Let's be smart about the shape of the AST for types.
|||
||| We reduce the *raw* AST to a single tree in which the node values
||| represent extra information about the children.
module Ola.Raw.Types.View

import Toolkit.Data.Location

import Ola.Types
import Ola.Raw.Types

%default total

mutual
  public export
  data Args : (rs : List (FileContext, Raw.Ty))
                 -> Type
    where
      Empty : Args Nil

      Extend : (fc   : FileContext)
            -> (ty   : Ty   r)
            -> (rest : Args rs)
                    -> Args (MkPair fc r :: rs)

  public export
  data Ty : (r    : Raw.Ty)
                 -> Type
    where
      TyVar : (r : Ref)
                -> Ty (TyVar r)

      TyChar : (fc : FileContext) -> Ty (TyNull fc CHAR)
      TyStr  : (fc : FileContext) -> Ty (TyNull fc STR)
      TyInt  : (fc : FileContext) -> Ty (TyNull fc INT)
      TyBool : (fc : FileContext) -> Ty (TyNull fc BOOL)
      TyUnit : (fc : FileContext) -> Ty (TyNull fc UNIT)

      TyArray : (fc : FileContext)
             -> (n  : Int)
             -> (ty : Ty t)
                   -> Ty (TyArray fc t n)

      TyPair : (fc : FileContext)
            -> (l  : Ty lr)
            -> (r  : Ty rr)
                  -> Ty (TyBi fc PAIR lr rr)

      TyUnion : (fc : FileContext)
             -> (l  : Ty                lr)
             -> (r  : Ty                   rr)
                   -> Ty (TyBi fc UNION lr rr)

      TyRef : (fc : FileContext)
           -> (ty : Ty           type)
                 -> Ty (TyRef fc type)

      TyHandle : (fc : FileContext)
              -> (k  : HandleKind)
                    -> Ty (TyHandle fc k)

      TyFunc : (fc    : FileContext)
            -> (argty : Args          as)
            -> (retty : Ty               r)
                     -> Ty (TyFunc fc as r)

mutual
  viewArgs : (rs : List (FileContext, Raw.Ty))
                -> Args rs
  viewArgs []
    = Empty
  viewArgs ((fc,x) :: xs)
    = Extend fc (view x) (viewArgs xs)

  export
  view : (r : Raw.Ty)
           -> Ty r

  view (TyNull fc CHAR)
    = TyChar fc
  view (TyNull fc STR)
    = TyStr fc
  view (TyNull fc INT)
    = TyInt fc
  view (TyNull fc BOOL)
    = TyBool fc
  view (TyNull fc UNIT)
    = TyUnit fc

  view (TyRef fc r)
    = TyRef fc (view r)

  view (TyBi fc PAIR a b)
    = TyPair fc (view a) (view b)
  view (TyBi fc UNION a b)
    = TyUnion fc (view a) (view b)

  view (TyFunc fc fcs y)
    = TyFunc fc (viewArgs fcs) (view y)

  view (TyArray fc n t)
    = TyArray fc t (view n)

  view (TyHandle fc k)
    = TyHandle fc k

  view (TyVar fc)
    = TyVar fc

-- [ EOF ]
