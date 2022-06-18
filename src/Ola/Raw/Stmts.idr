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

public export
data Unary = PRINT Raw.Expr
           | SEQ   Raw.Expr
           | LET   Raw.Ty Raw.Expr

public export
data Binary = WHILE Raw.Expr

public export
data Ternery = MATCH Raw.Expr
             | COND  Raw.Expr

namespace Raw
  public export
  data Stmt : Type where
    Null : FileContext -> Stmts.Nullary -> Stmt
    Un  : FileContext -> Stmts.Unary -> Stmt -> Stmt
    Bin : FileContext -> Stmts.Binary -> Stmt -> Stmt -> Stmt
    Tri : FileContext -> Stmts.Ternery -> Stmt -> Stmt -> Stmt -> Stmt

export
setSource : String -> Raw.Stmt -> Raw.Stmt
setSource new (Null fc k)
  = Null (setSource new fc) k

setSource new (Un fc k a)
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
  data Stmt : (s : Raw.Stmt) -> Type where
    Let : (fc : FileContext)
       -> (ty : Ty t)
       -> (ex : Expr e)
       -> (scope : Stmt rest)
                -> Stmt (Un fc (LET t e) rest)

    Seq : (fc   : FileContext)
       -> (this : Expr e)
       -> (rest : Stmt r)
               -> Stmt (Un fc (SEQ e) r)

    Cond : (fc : FileContext)
        -> (co  : Expr c)
        -> (tt : Stmt t)
        -> (ff : Stmt f)
        -> (rest : Stmt r)
                -> Stmt (Tri fc (COND c) t f r)

    Match : (fc   : FileContext)
         -> (co   : Expr c)
         -> (le    : Stmt t)
         -> (ri    : Stmt f)
         -> (rest : Stmt r)
                 -> Stmt (Tri fc (MATCH c) t f r)

    While : (fc  : FileContext)
         -> (co  : Expr c)
         -> (body  : Stmt b)
         -> (rest : Stmt r)
                 -> Stmt (Bin fc (WHILE c) b r)

    Print : (fc   : FileContext)
         -> (this : Expr e)
         -> (rest : Stmt r)
                 -> Stmt (Un fc (PRINT e) r)

    Return : (fc   : FileContext)
          -> (this : Expr e)
                  -> Stmt (Null fc (RET e))

    End : (fc   : FileContext)
               -> Stmt (Null fc END)

  export
  expand : (s : Raw.Stmt) -> Stmt s
  expand (Null fc END)
    = End fc
  expand (Null fc (RET x))
    = Return fc (expand x)

  expand (Un fc (PRINT x) u)
    = Print fc (expand x) (expand u)

  expand (Un fc (SEQ x) u)
    = Seq fc (expand x) (expand u)

  expand (Un fc (LET x y) u)
    = Let fc (expand x) (expand y) (expand u)

  expand (Bin fc (WHILE x) a b)
    = While fc (expand x) (expand a) (expand b)

  expand (Tri fc (MATCH x) a b c)
    = Match fc (expand x) (expand a) (expand b) (expand c)
  expand (Tri fc (COND x) a b c)
    = Cond fc (expand x) (expand a) (expand b) (expand c)


-- [ EOF ]
