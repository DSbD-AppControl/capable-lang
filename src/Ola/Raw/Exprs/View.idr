||| Turn the abstract AST to something more precise.
|||
||| Module    : Ola.Raw.Exprs.View
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
module Ola.Raw.Exprs.View

import Toolkit.Data.Location
import Toolkit.Data.DList

import Ola.Types
import Ola.Raw.Types
import Ola.Raw.Types.View

import Ola.Raw.Exprs

%default total

public export
data Expr : (s : Raw.Expr) -> Type where
  Var : (ref : Ref) -> Expr (Var ref)

  U : (fc : FileContext) ->                 Expr (Const fc UNIT v)
  C : (fc : FileContext) -> (v : Char  ) -> Expr (Const fc CHAR v)
  S : (fc : FileContext) -> (v : String) -> Expr (Const fc STR  v)
  I : (fc : FileContext) -> (v : Nat   ) -> Expr (Const fc INT  v)
  B : (fc : FileContext) -> (v : Bool  ) -> Expr (Const fc BOOL v)

  Cond : (fc : FileContext)
      -> (c  : Expr cond)
      -> (t  : Expr tt)
      -> (f  : Expr ff)
            -> Expr (Tri fc COND cond tt ff)

  Index : (fc : FileContext)
       -> (n  : Nat)
       -> (arr : Expr a)
              -> Expr (Un fc (INDEX n) a)

  Pair : (fc : FileContext)
      -> (l  : Expr f)
      -> (r  : Expr s)
            -> Expr (Bin fc PAIR f s )

  Left : (fc : FileContext)
      -> (p  : Expr pair)
            -> Expr (Un fc LEFT pair)

  Right : (fc : FileContext)
        -> (p  : Expr pair)
              -> Expr (Un fc RIGHT pair)


  Fetch : (fc : FileContext)
       -> (p  : Expr pair)
             -> Expr (Un fc FETCH pair)

  Open : (fc : FileContext)
      -> (k  : HandleKind)
      -> (w  : Expr s)
            -> Expr (Un fc (OPEN k) s)

  Read : (fc : FileContext)
      -> (p  : Expr pair)
            -> Expr (Un fc READ pair)

  Write : (fc : FileContext)
       -> (l  : Expr f)
       -> (r  : Expr s)
             -> Expr (Bin fc WRITE f s )

  Close : (fc : FileContext)
       -> (p  : Expr pair)
             -> Expr (Un fc CLOSE pair)

  Call : (fc : FileContext)
      -> (l  : Expr f)
      -> (r  : DList Raw.Expr Expr as)
            -> Expr (Call fc f as)

  The : (fc  : FileContext)
     -> (ty  : Ty t)
     -> (epr : Expr e)
            -> Expr (Un fc (THE t) e)

  Null : (fc : FileContext)
            -> Expr (Null fc)

  ArrayCons : (fc : FileContext)
           -> (l  : Expr h)
           -> (r  : Expr t)
                 -> Expr (Bin fc ARRAYCONS h t)

export
view : (s : Raw.Expr) -> Expr s
view (Var x)
  = Var x

view (Const fc UNIT val)
  = U fc
view (Const fc CHAR val)
  = C fc val
view (Const fc STR val)
  = S fc val
view (Const fc INT val)
  = I fc val
view (Const fc BOOL val)
  = B fc val

view (Un fc LEFT e) = Left fc (view e)
view (Un fc RIGHT e) = Right fc (view e)
view (Un fc FETCH e) = Fetch fc (view e)
view (Un fc READ e) = Read fc (view e)
view (Un fc CLOSE e) = Close fc (view e)
view (Un fc (INDEX x) e)
  = Index fc x (view e)
view (Un fc (OPEN x) e)
  = Open fc x (view e)

view (Un fc (THE x) e) with (view x)
  view (Un fc (THE x) e) | ty = The fc ty (view e)

view (Bin fc PAIR a b)
  = Pair fc (view a) (view b)

view (Bin fc WRITE a b)
  = Write fc (view a) (view b)

view (Tri fc COND a b c)
  = Cond fc (view a) (view b) (view c)

view (Null fc)
  = Null fc

view (Call fc a bs)
  = Call fc (view a) (viewArgs bs)
  where
    viewArgs : (as : List Expr) -> DList Expr Expr as
    viewArgs [] = []
    viewArgs (x :: xs)
      = view x :: viewArgs xs

view (Bin fc ARRAYCONS h t)
  = ArrayCons fc (view h) (view t)

export
getFC : {e : Expr} -> Expr e -> FileContext
getFC {e} x = getFC e

-- [ EOF ]
