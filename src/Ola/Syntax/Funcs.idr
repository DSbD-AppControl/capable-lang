||| AST for Funcs
|||
||| Module    : Syntax/Funcs.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
||| Let's be smart about the shape of the tree.
module Ola.Syntax.Funcs

import Toolkit.Data.Location

import Ola.Types
import Ola.Syntax.Types
import Ola.Syntax.Exprs
import Ola.Syntax.Stmts

%default total

data Nullary = PLAIN Syntax.Stmt
             | REC Syntax.Stmt

namespace Syntax
  public export
  data Func : Type where
    Null : FileContext -> Funcs.Nullary -> Func


export
setSource : String -> Syntax.Func -> Syntax.Func
setSource new (Null fc k)
  = Null (setSource new fc) k



namespace View

  public export
  data Func : (s : Syntax.Func) -> Type where
    Plain : (fc : FileContext)
         -> (scope : Stmt s)
                  -> Func (Null fc (PLAIN s))
    Rec : (fc : FileContext)
         -> (scope : Stmt s)
                  -> Func (Null fc (REC s))



  export
  expand : (s : Syntax.Func) -> Func s
  expand (Null fc (PLAIN x))
    = Plain fc (expand x)
  expand (Null fc (REC x))
    = Rec fc (expand x)
-- [ EOF ]
