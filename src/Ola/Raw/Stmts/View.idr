||| Turn the abstract AST to something more precise.
|||
||| Module    : Ola.Raw.Stmts.View
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
module Ola.Raw.Stmts.View

import Toolkit.Data.Location
import Toolkit.Data.DList

import Ola.Types
import Ola.Raw.Types
import Ola.Raw.Types.View

import Ola.Raw.Exprs
import Ola.Raw.Exprs.View

import Ola.Raw.Stmts

%default total

public export
data Stmt : (s : Raw.Stmt) -> Type where
  End : (fc : FileContext)
           -> Stmt (Null fc END)

  Ret : (fc : FileContext)
     -> (e  : Expr expr)
           -> Stmt (Null fc (RET expr))

  Print : (fc    : FileContext)
       -> (e     : Expr expr)
       -> (scope : Stmt body)
                -> Stmt (Un fc (PRINT expr) body)

  LetTy : (fc    : FileContext)
       -> (this  : Ref)
       -> (ty    : Ty t)
       -> (val   : Expr v)
       -> (scope : Stmt body)
                -> Stmt (Un fc (LET this (Just t) v) body)

  Let : (fc    : FileContext)
     -> (this  : Ref)
     -> (val   : Expr v)
     -> (scope : Stmt body)
              -> Stmt (Un fc (LET this Nothing v) body)

  VarTy : (fc    : FileContext)
       -> (this  : Ref)
       -> (ty    : Ty t)
       -> (val   : Expr v)
       -> (scope : Stmt body)
                -> Stmt (Un fc (VAR this (Just t) v) body)

  Var : (fc    : FileContext)
     -> (this  : Ref)
     -> (val   : Expr v)
     -> (scope : Stmt body)
              -> Stmt (Un fc (VAR this Nothing v) body)

  Mutate : (fc    : FileContext)
        -> (ref   : Expr r)
        -> (value : Expr v)
        -> (scope : Stmt body)
                 -> Stmt (Un fc (MUTATE r v) body)

  Run : (fc    : FileContext)
     -> (val   : Expr v)
     -> (scope : Stmt body)
              -> Stmt (Un fc (RUN v) body)

  While : (fc : FileContext)
       -> (cond : Expr c)
       -> (body : Stmt b)
       -> (rest : Stmt r)
               -> Stmt (Bin fc (WHILE c) b r)

  Split : (fc    : FileContext)
       -> (pair  : Expr p)
       -> (a     : Ref)
       -> (b     : Ref)
       -> (scope : Stmt body)
                -> Stmt (Un fc (SPLIT p a b) body)

  Match : (fc     : FileContext)
       -> (cond   : Expr c)
       -> (l      : Ref)
       -> (scopeL : Stmt bodyL)
       -> (r      : Ref)
       -> (scopeR : Stmt bodyR)
       -> (rest   : Stmt rem)
                 -> Stmt (Tri fc (MATCH c l r) bodyL bodyR rem)

  Cond : (fc     : FileContext)
      -> (cond   : Expr c)
      -> (scopeT : Stmt bodyT)
      -> (scopeF : Stmt bodyF)
      -> (rest   : Stmt rem)
                -> Stmt (Tri fc (COND c) bodyT bodyF rem)

export
view : (s : Raw.Stmt) -> Stmt s
view (Null fc END)
  = End fc
view (Null fc (RET x))
  = Ret fc (view x)

view (Un fc (PRINT x) rest)
  = Print fc (view x) (view rest)

view (Un fc (LET r Nothing v) rest)
  = Let fc r (view v) (view rest)

view (Un fc (LET r (Just ty) v) rest)
  = LetTy fc r (view ty) (view v) (view rest)

view (Un fc (VAR r Nothing v) rest)
  = Var fc r (view v) (view rest)

view (Un fc (VAR r (Just ty) v) rest)
  = VarTy fc r (view ty) (view v) (view rest)

view (Un fc (MUTATE r v) rest)
  = Mutate fc (view r) (view v) (view rest)

view (Un fc (RUN x) rest)
  = Run fc (view x) (view rest)

view (Un fc (SPLIT p l r) rest)
  = Split fc (view p) l r (view rest)

view (Bin fc (WHILE c) s b)
  = While fc (view c) (view s) (view b)

view (Tri fc (MATCH c rl rr) l r b)
  = Match fc (view c) rl (view l) rr (view r) (view b)

view (Tri fc (COND c) t f b)
  = Cond fc (view c) (view t) (view f) (view b)

export
getFC : {s : Stmt} -> Stmt s -> FileContext
getFC {s} _ = getFC s

-- [ EOF ]
