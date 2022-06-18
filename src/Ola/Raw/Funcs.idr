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

data Nullary = PLAIN Raw.Stmt
             | REC Raw.Stmt

namespace Raw
  public export
  data Func : Type where
    Null : FileContext -> Funcs.Nullary -> Func


export
setSource : String -> Raw.Func -> Raw.Func
setSource new (Null fc k)
  = Null (setSource new fc) k



namespace View

  public export
  data Func : (s : Raw.Func) -> Type where
    Plain : (fc : FileContext)
         -> (scope : Stmt s)
                  -> Func (Null fc (PLAIN s))
    Rec : (fc : FileContext)
         -> (scope : Stmt s)
                  -> Func (Null fc (REC s))



  export
  expand : (s : Raw.Func) -> Func s
  expand (Null fc (PLAIN x))
    = Plain fc (expand x)
  expand (Null fc (REC x))
    = Rec fc (expand x)
-- [ EOF ]
