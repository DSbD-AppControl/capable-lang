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
import Ola.Raw.Types
import Ola.Raw.Exprs
import Ola.Raw.Stmts
import Ola.Raw.Funcs

-- @TODO Add in for and foreach directly into syntax. Will elaborate later.

%default total

data Nullary = MAIN Raw.Stmt

data Unary = DEFTYPE Raw.Ty
           | DEFFUNC  Raw.Ty Raw.Func

namespace Raw
  public export
  data Prog : Type where
    Null : FileContext -> Progs.Nullary -> Prog
    Un : FileContext -> Progs.Unary -> Prog -> Prog


export
setSource : String -> Raw.Prog -> Raw.Prog

setSource new (Null fc k)
  = Null (setSource new fc) k

setSource new (Un fc k a)
  = Un (setSource new fc)
       k
       (setSource new a)

namespace View

  public export
  data Prog : (s : Raw.Prog) -> Type where
    TypeDef : (fc : FileContext)
           -> (type  : Ty s)
           -> (p     : Prog r)
                    -> Prog (Un fc (DEFTYPE s) r)

    DefFunc : (fc  : FileContext)
           -> (sig : Ty t)
           -> (def : Func s)
           -> (p   : Prog r)
                    -> Prog (Un fc (DEFFUNC t s) r)

    Main : (fc : FileContext)
        -> (scope : Stmt s)
                 -> Prog (Null fc (MAIN s))



  export
  expand : (s : Raw.Prog) -> Prog s
  expand (Null fc (MAIN x))
    = Main fc (expand x)

  expand (Un fc (DEFTYPE x) p)
    = TypeDef fc (expand x) (expand p)

  expand (Un fc (DEFFUNC x y) p)
    = DefFunc fc (expand x) (expand y) (expand p)

-- [ EOF ]
