||| AST for Statements
|||
||| Module    : Raw/Stmts.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
||| Let's be smart about the shape of the tree.
module Ola.Raw.Stmts

import Toolkit.Data.Location

import Ola.Types
import Ola.Raw.Types
import Ola.Raw.Exprs

%default total

public export
data Nullary = END | RET Raw.Expr

Show Stmts.Nullary where
  show END = "END"
  show (RET x)
    = "(RET \{show x}})"

setSourceN : String -> Stmts.Nullary -> Stmts.Nullary
setSourceN str END
  = END
setSourceN str (RET x)
  = RET (setSource str x)

public export
data Unary = PRINT Raw.Expr
           | LET   Ref (Maybe Raw.Ty) Raw.Expr
           | VAR   Ref (Maybe Raw.Ty) Raw.Expr
           | MUTATE Raw.Expr Raw.Expr
           | RUN Raw.Expr
           | SPLIT Raw.Expr Ref Ref

Show Stmts.Unary where
  show (PRINT x)    = "(PRINT \{show x})"
  show (LET x t y)  = "(LET \{show x} \{show t} \{show y})"
  show (VAR x t y)  = "(VAR \{show x} \{show t} \{show y})"
  show (MUTATE x y) = "(MUTATE \{show x} \{show y})"
  show (RUN x)      = "(RUN \{show x})"
  show (SPLIT x y z) = "(SPLIT \{show x} \{show y} \{show z})"

setSourceU : String -> Stmts.Unary -> Stmts.Unary
setSourceU new (PRINT x)
  = PRINT (setSource new x)

setSourceU new (LET x t y)
  = LET (setSource new x)
        (map (setSource new) t)
        (setSource new y)

setSourceU new (VAR x t y)
  = VAR (setSource new x)
        (map (setSource new) t)
        (setSource new y)

setSourceU new (MUTATE x y)
  = MUTATE (setSource new x)
           (setSource new y)

setSourceU new (RUN x)
  = RUN (setSource new x)
setSourceU new (SPLIT x y z)
  = SPLIT (setSource new x)
          (setSource new y)
          (setSource new z)


public export
data Binary = WHILE Raw.Expr


Show Stmts.Binary where
  show (WHILE x)     = "(WHILE \{show x})"


setSourceB : String -> Stmts.Binary -> Stmts.Binary
setSourceB str (WHILE x)
  = WHILE (setSource str x)


public export
data Ternery = MATCH Raw.Expr Ref Ref
             | COND  Raw.Expr

Show Stmts.Ternery where
  show (MATCH x y z) = "(MATCH \{show x} \{show y} \{show z})"
  show (COND x)      = "(COND \{show x})"

setSourceT : String -> Stmts.Ternery -> Stmts.Ternery
setSourceT str (MATCH x y z)
  = MATCH (setSource str x)
          (setSource str y)
          (setSource str z)

setSourceT str (COND x)
  = COND (setSource str x)


namespace Raw
  public export
  data Stmt : Type where
    Null : FileContext -> Stmts.Nullary -> Stmt
    Un  : FileContext -> Stmts.Unary -> Stmt -> Stmt
    Bin : FileContext -> Stmts.Binary -> Stmt -> Stmt -> Stmt
    Tri : FileContext -> Stmts.Ternery -> Stmt -> Stmt -> Stmt -> Stmt

export
Show Raw.Stmt where
  show (Null x y)      = "(Null \{show x} \{show y})"
  show (Un x y z)      = "(Un   \{show x} \{show y} \{show z})"
  show (Bin x y z w)   = "(Bin  \{show x} \{show y} \{show z} \{show w})"
  show (Tri x y z w v) = "(Tri  \{show x} \{show y} \{show z} \{show w} \{show v})"

export
setSource : String -> Raw.Stmt -> Raw.Stmt
setSource new (Null fc k)
  = Null (setSource new fc)
         (setSourceN new k)

setSource new (Un fc k a)
  = Un (setSource  new fc)
       (setSourceU new k)
       (setSource  new a)

setSource new (Bin fc k a b)
  = Bin (setSource new fc)
       (setSourceB new k)
       (setSource new a)
       (setSource new b)

setSource new (Tri fc k a b c)
  = Tri (setSource new fc)
       (setSourceT new k)
       (setSource new a)
       (setSource new b)
       (setSource new c)

export
getFC : Stmt -> FileContext
getFC (Null x y) = x
getFC (Un x y z) = x
getFC (Bin x y z w) = x
getFC (Tri x y z w v) = x

-- [ EOF ]
