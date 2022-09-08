||| AST for Funcs
|||
||| Module    : Raw/Funcs.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
||| Let's be smart about the shape of the tree.
module Ola.Raw.Funcs

import Toolkit.Data.Location

import Ola.Types
import Ola.Raw.Types
import Ola.Raw.Exprs
import Ola.Raw.Stmts

%default total

public export
data Nullary
  = FUNC (List (FileContext, Ref, Raw.Ty))  -- Args
         Raw.Ty                             -- Return
         Raw.Stmt                           -- Body
         Raw.Expr                           -- Last Expr

Show Funcs.Nullary where
  show (FUNC xs x y z)
    = "(FUNC \{show xs} \{show x} \{show y} \{show z})"


setSourceA : String -> (FileContext, Ref, Raw.Ty) -> (FileContext, Ref, Raw.Ty)
setSourceA str (x, y, z)
  = (setSource str x, setSource str y, setSource str z)

setSourceAS : String -> List (FileContext, Ref, Raw.Ty) -> List (FileContext, Ref, Raw.Ty)
setSourceAS str []
  = []

setSourceAS str (x :: xs)
  = setSourceA str x :: setSourceAS str xs

setSourceN : String -> Funcs.Nullary -> Funcs.Nullary
setSourceN str (FUNC xs x y z)
  = FUNC (setSourceAS str xs)
         (setSource str x)
         (setSource str y)
         (setSource str z)

namespace Raw
  public export
  data Func : Type where
    Null : FileContext -> Funcs.Nullary -> Func

export
Show Raw.Func where
  show (Null x y) = "(Null \{show x} \{show y})"

export
setSource : String -> Raw.Func -> Raw.Func
setSource new (Null fc k)
  = Null (setSource new fc)
         (setSourceN new k)

export
getFC : Raw.Func -> FileContext
getFC (Null x y) = x

-- [ EOF ]
