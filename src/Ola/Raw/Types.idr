||| AST for types.
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
module Ola.Raw.Types

import Toolkit.Data.Location

import Ola.Types

%default total

public export
data Nullary = CHAR | STR | INT | BOOL | UNIT

Show Nullary where
  show CHAR = "CHAR"
  show STR  = "STR"
  show INT  = "INT"
  show BOOL = "BOOL"
  show UNIT = "UNIT"

public export
data Binary = PAIR | UNION

Show Binary where
  show PAIR  = "PAIR"
  show UNION = "UNION"

namespace Raw
  public export
  data Ty = TyNull FileContext Nullary
          | TyRef FileContext Raw.Ty

          | TyBi FileContext Binary Raw.Ty Raw.Ty

          | TyFunc FileContext (List (FileContext, Raw.Ty))
                               Raw.Ty

          | TyArray FileContext Raw.Ty Nat

          | TyHandle FileContext HandleKind

          | TyVar Ref


mutual
  setSourceA : String -> (FileContext, Raw.Ty)
                      -> (FileContext, Raw.Ty)
  setSourceA str (fc,ty)
    = (setSource str fc, setSource str ty)

  setSourceAS : String -> List (FileContext,  Raw.Ty)
                       -> List (FileContext,  Raw.Ty)
  setSourceAS str [] = []
  setSourceAS str (x :: xs)
    = setSourceA str x :: setSourceAS str xs

  export
  setSource : String -> Raw.Ty -> Raw.Ty
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

  setSource new (TyFunc fc args ret)
    = TyFunc (setSource new fc)
             (setSourceAS new args)
             (setSource new ret)

  setSource new (TyArray fc type nat)
    = TyArray (setSource new fc)
              (setSource new type)
              nat

  setSource new (TyHandle fc kind)
    = TyHandle (setSource new fc)
               kind

  setSource new (TyVar fc)
    = TyVar ({span $= setSource new} fc)

mutual
  showA : (FileContext, Raw.Ty) -> String
  showA (x, z)
    = "(\{show x}, \{showT z})"

  showTS : List (FileContext, Raw.Ty) -> String
  showTS Nil = "Nil"
  showTS (x::xs) = "\{showA x} :: \{showTS xs}"

  showT : Raw.Ty -> String
  showT (TyNull x y)     = "(TyNull \{show x} \{show y})"
  showT (TyRef x y)      = "(TyRef \{show x} \{showT y})"
  showT (TyBi x y z w)   = "(TyBi \{show x} \{show y} \{showT z} \{showT w})"
  showT (TyFunc fc as r) = "(TyFunc \{show fc} (\{showTS as}) \{showT r})"
  showT (TyArray x y k)  = "(TyArray \{show x} \{showT y} \{show k})"
  showT (TyHandle x y)   = "(TyHandle \{show x} \{show y})"
  showT (TyVar x)        = "(TyVar {\show x})"

export
Show Raw.Ty where
  show = showT


export
getFC : Raw.Ty -> FileContext
getFC (TyNull fc y) = fc
getFC (TyRef fc y) = fc
getFC (TyBi fc y z w) = fc
getFC (TyFunc fc fcs y) = fc
getFC (TyArray fc y k) = fc
getFC (TyHandle fc y) = fc
getFC (TyVar fc) = span fc

-- [ EOF ]
