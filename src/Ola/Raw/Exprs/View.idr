||| Turn the abstract AST to something more precise.
|||
||| Module    : Ola.Raw.Exprs.View
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
module Ola.Raw.Exprs.View

import System.File.Mode
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
  I : (fc : FileContext) -> (v : Int   ) -> Expr (Const fc INT  v)
  B : (fc : FileContext) -> (v : Bool  ) -> Expr (Const fc BOOL v)

  ToString : (fc : FileContext) -> (l : Expr a)                 -> Expr (Un  fc TOSTR a)

  And : (fc : FileContext) -> (l : Expr a) -> (r : Expr b) -> Expr (Bin fc AND a b)
  Or  : (fc : FileContext) -> (l : Expr a) -> (r : Expr b) -> Expr (Bin fc OR  a b)
  Not : (fc : FileContext) -> (l : Expr a)                 -> Expr (Un  fc NOT a)

  LT  : (fc : FileContext) -> (l : Expr a) -> (r : Expr b) -> Expr (Bin fc LT  a b)
  LTE : (fc : FileContext) -> (l : Expr a) -> (r : Expr b) -> Expr (Bin fc LTE  a b)
  GT  : (fc : FileContext) -> (l : Expr a) -> (r : Expr b) -> Expr (Bin fc GT  a b)
  GTE : (fc : FileContext) -> (l : Expr a) -> (r : Expr b) -> Expr (Bin fc GTE  a b)
  EQ  : (fc : FileContext) -> (l : Expr a) -> (r : Expr b) -> Expr (Bin fc EQ  a b)

  Sub : (fc : FileContext) -> (l : Expr a) -> (r : Expr b) -> Expr (Bin fc SUB a b)
  Div : (fc : FileContext) -> (l : Expr a) -> (r : Expr b) -> Expr (Bin fc DIV a b)
  Mul : (fc : FileContext) -> (l : Expr a) -> (r : Expr b) -> Expr (Bin fc MUL a b)
  Add : (fc : FileContext) -> (l : Expr a) -> (r : Expr b) -> Expr (Bin fc ADD a b)

  Size : (fc : FileContext) -> (l : Expr a) -> Expr (Un  fc SIZE a)
  Cons : (fc : FileContext) -> (l : Expr a) -> (r : Expr b) -> Expr (Bin fc CONS  a b)

  Ord : (fc : FileContext) -> (l : Expr a) -> Expr (Un  fc ORD  a)
  Chr : (fc : FileContext) -> (l : Expr a) -> Expr (Un  fc CHR  a)
  Str : (fc : FileContext) -> (l : Expr a) -> Expr (Un  fc STRO a)

  Slice : (fc : FileContext) -> (l : Expr a) -> (k : Expr b) -> (j : Expr c) -> Expr (Tri  fc SLICE a b c)


  Cond : (fc : FileContext)
      -> (c  : Expr cond)
      -> (t  : Expr tt)
      -> (f  : Expr ff)
            -> Expr (Tri fc COND cond tt ff)

  Index : (fc : FileContext)
       -> (n  : Int)
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
      -> (m  : Mode)
      -> (w  : Expr s)
            -> Expr (Un fc (OPEN k m) s)

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
view (Un fc (OPEN x m) e)
  = Open fc x m (view e)

view (Un fc (THE x) e) with (view x)
  view (Un fc (THE x) e) | ty = The fc ty (view e)

view (Un fc NOT e)
  = Not fc (view e)
view (Un fc SIZE e)
  = Size fc (view e)
view (Un fc ORD e)
  = Ord fc (view e)

view (Un fc CHR e)
  = Chr fc (view e)

view (Un fc STRO e)
  = Str fc (view e)

view (Un fc TOSTR e)
  = ToString fc (view e)

view (Bin fc AND a b)
  = And fc (view a) (view b)
view (Bin fc OR  a b)
  = Or  fc (view a) (view b)

view (Bin fc LT  a b) = LT fc (view a) (view b)
view (Bin fc LTE a b) = LTE fc (view a) (view b)
view (Bin fc EQ  a b) = EQ fc (view a) (view b)
view (Bin fc GT  a b) = GT fc (view a) (view b)
view (Bin fc GTE a b) = GTE fc (view a) (view b)

view (Bin fc ADD a b)  = Add  fc (view a) (view b)
view (Bin fc MUL a b)  = Mul  fc (view a) (view b)
view (Bin fc SUB a b)  = Sub  fc (view a) (view b)
view (Bin fc DIV a b)  = Div  fc (view a) (view b)
view (Bin fc CONS a b) = Cons fc (view a) (view b)


view (Bin fc PAIR a b)
  = Pair fc (view a) (view b)

view (Bin fc WRITE a b)
  = Write fc (view a) (view b)

view (Tri fc SLICE a b c)
  = Slice fc (view a) (view b) (view c)

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
