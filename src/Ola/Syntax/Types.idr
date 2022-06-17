||| AST for types.
|||
||| Module    : Types.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
|||
||| Let's be smart about the shape of the tree.
module Ola.Syntax.Types

import Toolkit.Data.Location

import Ola.Types

%default total

public export
data Nullary = CHAR | STR | INT | BOOL | UNIT


public export
data Binary = PAIR | UNION | FUNC

namespace Syntax
  public export

  data Ty = TyNull FileContext Nullary
          | TyRef FileContext Syntax.Ty
          | TyBi FileContext Binary Syntax.Ty Syntax.Ty

          | TyArray FileContext Syntax.Ty Nat

          | TyHandle FileContext HandleKind

          | TyVar Ref


export
setSource : String -> Syntax.Ty -> Syntax.Ty
setSource new (TyNull fc kind)
  = TyNull (setSource new fc) kind

setSource new (TyRef fc v)
  = TyRef (setSource new fc)
          (setSource new v)
setSource new (TyBi fc kind a b)
  = TyBi (setSource new fc)
         kind
         (setSource new a)
         (setSource new b)

setSource new (TyArray fc type nat)
  = TyArray (setSource new fc)
            (setSource new type)
            nat

setSource new (TyHandle fc kind)
  = TyHandle (setSource new fc)
             kind

setSource new (TyVar fc)
  = TyVar ({span $= setSource new} fc)


namespace View
  public export
  data Ty : (type : Syntax.Ty) -> Type where
    TyVar  : (ref : Ref)        -> Ty (TyVar ref)
    TyChar : (fc : FileContext) -> Ty (TyNull fc CHAR)
    TyStr  : (fc : FileContext) -> Ty (TyNull fc STR)
    TyInt  : (fc : FileContext) -> Ty (TyNull fc INT)
    TyBool : (fc : FileContext) -> Ty (TyNull fc BOOL)
    TyUnit : (fc : FileContext) -> Ty (TyNull fc UNIT)

    TyArray : (fc : FileContext) -> Ty type -> (n : Nat) -> Ty (TyArray fc type n)




    TyPair : (fc : FileContext)
          -> (l  : Ty f)
          -> (r  : Ty s)
                -> Ty (TyBi fc PAIR f s)

    TyUnion : (fc : FileContext)
           -> (l  : Ty f)
           -> (r  : Ty s)
                 -> Ty (TyBi fc UNION f s)

    TyRef : (fc : FileContext) -> Ty type -> Ty (TyRef fc type)

    TyHandle : (fc : FileContext)
            -> (k : HandleKind)
                 -> Ty (TyHandle fc k)

    TyFunc : (fc : FileContext)
          -> (arg : Ty a)
          -> (ret : Ty r)
                 -> Ty (TyBi fc FUNC a r)

  export
  expand : (s : Syntax.Ty) -> Ty s
  expand (TyNull fc CHAR)
    = TyChar fc
  expand (TyNull fc STR)
    = TyStr fc
  expand (TyNull fc INT)
    = TyInt fc
  expand (TyNull fc BOOL)
    = TyBool fc
  expand (TyNull fc UNIT)
    = TyUnit fc

  expand (TyRef fc ref)
    = TyRef fc (expand ref)

  expand (TyBi fc PAIR a b)
    = TyPair fc (expand a) (expand b)
  expand (TyBi fc UNION a b)
    = TyUnion fc (expand a) (expand b)
  expand (TyBi fc FUNC a b)
    = TyFunc fc (expand a) (expand b)

  expand (TyArray fc n t)
    = TyArray fc (expand n) t

  expand (TyHandle fc k)
    = TyHandle fc k

  expand (TyVar x) = TyVar x

-- [ EOF ]
