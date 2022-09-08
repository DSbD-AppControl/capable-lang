||| AST for Exprs.
|||
||| Module    : Exprs.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
||| Let's be smart about the shape of the tree.
module Ola.Raw.Exprs

import Toolkit.Data.Location

import Ola.Types
import Ola.Raw.Types

%default total

public export
data BinaryVal = UNIT | CHAR | STR | INT | BOOL

Show BinaryVal where
  show UNIT = "UNIT"
  show CHAR = "CHAR"
  show STR  = "STR"
  show INT  = "INT"
  show BOOL = "BOOL"

public export
InterpBVal : BinaryVal -> Type
InterpBVal UNIT = ()
InterpBVal CHAR = Char
InterpBVal STR = String
InterpBVal INT = Nat
InterpBVal BOOL = Bool

public export
data Unary = LEFT  | RIGHT
           | FETCH
           | READ  | CLOSE
           | INDEX Nat
           | OPEN HandleKind
           | THE Raw.Ty

Show Unary where
  show LEFT      = "LEFT"
  show RIGHT     = "RIGHT"
  show FETCH     = "FETCH"
  show READ      = "READ"
  show CLOSE     = "CLOSE"
  show (INDEX k) = "(INDEX \{show k})"
  show (OPEN x)  = "(OPEN \{show x})"
  show (THE x)   = "(THE \{show x})"

setSourceU : String -> Unary -> Unary
setSourceU new (THE x)
  = THE (setSource new x)
setSourceU _ x = x

public export
data Binary = PAIR | WRITE | ARRAYCONS

Show Exprs.Binary where
  show PAIR      = "PAIR"
  show WRITE     = "WRITE"
  show ARRAYCONS = "ARRAYCONS"

public export
data Ternery = COND

Show Exprs.Ternery where
  show COND = "COND"

namespace Raw
  public export
  data Expr : Type where
    Var : Ref -> Expr

    Const : FileContext -> (k : BinaryVal) -> (val : InterpBVal k) -> Expr

-- @TODO Primitive Ops
    Null : FileContext -> Expr
    Un  : FileContext -> Exprs.Unary -> Expr -> Expr
    Bin : FileContext -> Exprs.Binary -> Expr -> Expr -> Expr
    Tri : FileContext -> Ternery -> Expr -> Expr -> Expr -> Expr
    Call : FileContext -> Expr -> List Expr -> Expr

mutual
  showES : List Expr -> String
  showES [] = "Nil"
  showES (x :: xs)
    = "\{showE x} :: \{showES xs}"

  showE : Raw.Expr -> String
  showE (Var x)         = "(Var \{show x})"
  showE (Const x k val) = "(Const \{show x} \{show k} (VAL HIDDEN)" --@TODO Insert val
  showE (Null x)        = "(Null \{show x})"
  showE (Un x y z)      = "(Un \{show x} \{show y} \{showE z})"
  showE (Bin x y z w)   = "(Bin \{show x} \{show y} \{showE z} \{showE w})"
  showE (Tri x y z w v) = "(Tri \{show x} \{show y} \{showE z} \{showE w} \{showE v})"
  showE (Call x y xs)   = "(Call \{show x} \{showE y} (\{showES xs})"

export
Show Raw.Expr where
  show = showE

export
getFC : Expr -> FileContext
getFC (Var x) = span x
getFC (Const x k val) = x
getFC (Null x)        = x
getFC (Un x y z)      = x
getFC (Bin x y z w)   = x
getFC (Tri x y z w v) = x
getFC (Call x y xs)   = x

mutual
  setSourceXS : String -> List Raw.Expr -> List Raw.Expr
  setSourceXS str []
    = []
  setSourceXS str (x :: xs)
    = setSource str x :: setSourceXS str xs

  export
  setSource : String -> Raw.Expr -> Raw.Expr
  setSource new (Null fc)
    = Null (setSource new fc)

  setSource new (Var x)
    = Var ({span $= setSource new} x)

  setSource new (Const fc k val)
    = Const (setSource new fc) k val


  setSource new (Un fc k a )
    = Un (setSource  new fc)
         (setSourceU new k)
         (setSource  new a)

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
  setSource new (Call fc f fs)
    = Call (setSource new fc)
           (setSource new f)
           (setSourceXS new fs)

-- [ EOF ]
