||| AST for Exprs.
|||
||| Module    : Syntax/Exprs.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
||| Let's be smart about the shape of the tree.
module Ola.Syntax.Exprs

import Toolkit.Data.Location

import Ola.Types
import Ola.Syntax.Types

public export
data BinaryVal = UNIT | CHAR | STR | INT | BOOL

public export
InterpBVal : BinaryVal -> Type
InterpBVal UNIT = ()
InterpBVal CHAR = Char
InterpBVal STR = String
InterpBVal INT = Nat
InterpBVal BOOL = Bool

public export
data Unary = FIRST | SECOND
           | LEFT  | RIGHT
           | FETCH | ALLOC
           | READ  | CLOSE
           | INDEX Nat
           | OPEN HandleKind
           | THE Syntax.Ty

public export
data Binary = ARRAYCONS | PAIR | MUTATE | WRITE | CALL

public export
data Ternery = MATCH | COND

namespace Syntax
  public export
  data Expr : Type where
    Var : Ref -> Expr

    Const : FileContext -> (k : BinaryVal) -> (val : InterpBVal k) -> Expr

    ArrayEmpty : FileContext -> Expr
    Un  : FileContext -> Exprs.Unary -> Expr -> Expr
    Bin : FileContext -> Exprs.Binary -> Expr -> Expr -> Expr
    Tri : FileContext -> Ternery -> Expr -> Expr -> Expr -> Expr

export
setSource : String -> Syntax.Expr -> Syntax.Expr
setSource new (Var x)
  = Var ({span $= setSource new} x)

setSource new (Const fc k val)
  = Const (setSource new fc) k val

setSource new (ArrayEmpty fc)
  = ArrayEmpty (setSource new fc)


setSource new (Un fc k a )
  = Un (setSource new fc)
       k
       (setSource new a)

setSource new (Bin fc k a b)
  = Bin (setSource new fc)
        k
        (setSource new a)
        (setSource new b)

setSource new (Tri fc k a b c)
  = Tri (setSource new fc)
        k
        (setSource new a)
        (setSource new b)
        (setSource new c)

namespace View

  public export
  data Expr : (s : Syntax.Expr) -> Type where
    Var : (ref : Ref) -> Expr (Var ref)

    U : (fc : FileContext) ->           Expr (Const fc UNIT v)
    C : (fc : FileContext) -> (v : Char  ) -> Expr (Const fc CHAR v)
    S : (fc : FileContext) -> (v : String) -> Expr (Const fc STR  v)
    I : (fc : FileContext) -> (v : Nat   ) -> Expr (Const fc INT  v)
    B : (fc : FileContext) -> (v : Bool  ) -> Expr (Const fc BOOL v)

    Cond : (fc : FileContext)
        -> (c  : Expr cond)
        -> (t  : Expr tt)
        -> (f  : Expr ff)
              -> Expr (Tri fc COND cond tt ff)

    ArrayEmpty : (fc : FileContext) -> Expr (ArrayEmpty fc)
    ArrayCons : (fc : FileContext)
             -> (x  : Expr h)
             -> (xs : Expr t)
                   -> Expr (Bin fc ARRAYCONS h t)

    Index : (fc : FileContext)
         -> (n  : Nat)
         -> (arr : Expr a)
                -> Expr (Un fc (INDEX n) a)

    Pair : (fc : FileContext)
        -> (l  : Expr f)
        -> (r  : Expr s)
              -> Expr (Bin fc PAIR f s )

    First : (fc : FileContext)
         -> (p  : Expr pair)
               -> Expr (Un fc FIRST pair)

    Second : (fc : FileContext)
          -> (p  : Expr pair)
                -> Expr (Un fc SECOND pair)

    Left : (fc : FileContext)
        -> (p  : Expr pair)
              -> Expr (Un fc LEFT pair)

    Right : (fc : FileContext)
          -> (p  : Expr pair)
                -> Expr (Un fc RIGHT pair)

    Match : (fc : FileContext)
        -> (c  : Expr cond)
        -> (t  : Expr tt)
        -> (f  : Expr ff)
              -> Expr (Tri fc MATCH cond tt ff)

    Fetch : (fc : FileContext)
         -> (p  : Expr pair)
               -> Expr (Un fc FETCH pair)

    Alloc : (fc : FileContext)
         -> (p  : Expr pair)
               -> Expr (Un fc ALLOC pair)

    Mutate : (fc : FileContext)
          -> (l  : Expr f)
          -> (r  : Expr s)
                -> Expr (Bin fc MUTATE f s )

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
        -> (r  : Expr s)
              -> Expr (Bin fc CALL f s )

    The : (fc  : FileContext)
       -> (ty  : View.Ty t)
       -> (epr : Expr e)
              -> Expr (Un fc (THE t) e)

  export
  expand : (s : Syntax.Expr) -> Expr s
  expand (Var x)
    = Var x

  expand (Const fc UNIT val)
    = U fc
  expand (Const fc CHAR val)
    = C fc val
  expand (Const fc STR val)
    = S fc val
  expand (Const fc INT val)
    = I fc val
  expand (Const fc BOOL val)
    = B fc val

  expand (ArrayEmpty x)
    = ArrayEmpty x

  expand (Un fc FIRST e) = First fc (expand e)
  expand (Un fc SECOND e) = Second fc (expand e)
  expand (Un fc LEFT e) = Left fc (expand e)
  expand (Un fc RIGHT e) = Right fc (expand e)
  expand (Un fc FETCH e) = Fetch fc (expand e)
  expand (Un fc ALLOC e) = Alloc fc (expand e)
  expand (Un fc READ e) = Read fc (expand e)
  expand (Un fc CLOSE e) = Close fc (expand e)
  expand (Un fc (INDEX x) e)
    = Index fc x (expand e)
  expand (Un fc (OPEN x) e)
    = Open fc x (expand e)

  expand (Un fc (THE x) e) with (expand x)
    expand (Un fc (THE x) e) | ty = View.The fc ty (expand e)

  expand (Bin fc ARRAYCONS a b)
    = ArrayCons fc (expand a) (expand b)
  expand (Bin fc PAIR a b)
    = Pair fc (expand a) (expand b)
  expand (Bin fc MUTATE a b)
    = Mutate fc (expand a) (expand b)
  expand (Bin fc WRITE a b)
    = Write fc (expand a) (expand b)
  expand (Bin fc CALL a b)
    = Call fc (expand a) (expand b)

  expand (Tri fc MATCH a b c)
    = Match fc (expand a) (expand b) (expand c)
  expand (Tri fc COND a b c)
    = Cond fc (expand a) (expand b) (expand c)

-- [ EOF ]
