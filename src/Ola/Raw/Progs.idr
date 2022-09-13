||| AST for Progs
|||
||| Module    : Raw/Progs.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
||| Let's be smart about the shape of the tree.
module Ola.Raw.Progs

import Toolkit.Data.Location

import Ola.Types
import Ola.Raw.Roles
import Ola.Raw.Types
import Ola.Raw.Exprs
import Ola.Raw.Stmts
import Ola.Raw.Funcs


%default total

public export
data Nullary = MAIN Raw.Func

setSourceN : String -> Progs.Nullary -> Progs.Nullary
setSourceN str (MAIN f)
  = MAIN (setSource str f)

Show Progs.Nullary where
  show (MAIN a) = "(MAIN \{show a})"

public export
data Unary = DEFTYPE Ref  Raw.Ty
           | DEFFUNC Ref  Raw.Func
           | DEFROLE Ref  Raw.Role

Show Progs.Unary where
  show (DEFTYPE r ty) = "(DEFTYPE \{show r} \{show ty})"
  show (DEFFUNC r f)  = "(DEFFUNC \{show r} \{show f})"
  show (DEFROLE r ro) = "(DEFROLE \{show r} \{show ro})"

setSourceU : String -> Progs.Unary -> Progs.Unary
setSourceU str (DEFTYPE x y)

  = DEFTYPE (setSource str x)
            (setSource str y)

setSourceU str (DEFFUNC x y)
  = DEFFUNC (setSource str x)
            (setSource str y)

setSourceU str (DEFROLE x y)
  = DEFROLE (setSource str x)
            (setSource str y)



namespace Raw
  public export
  data Prog : Type where
    Null : FileContext -> Progs.Nullary -> Prog
    Un : FileContext -> Progs.Unary -> Prog -> Prog

export
Show Raw.Prog where
  show (Null x y) = "(Null \{show x} \{show y})"
  show (Un x y z) = "(Un   \{show x} \{show y} \{show z})"

export
setSource : String -> Raw.Prog -> Raw.Prog

setSource new (Null fc k)
  = Null (setSource new fc)
         (setSourceN new k)

setSource new (Un fc k a)
  = Un (setSource new fc)
                (setSourceU new k)
       (setSource new a)

export
getFC : (p : Raw.Prog) -> FileContext
getFC (Null x y) = x
getFC (Un x y z) = x
-- [ EOF ]
