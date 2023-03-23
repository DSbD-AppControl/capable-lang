||| Views on Sessions.
|||
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Capable.Raw.Sessions

import        System.File.Mode
import public Data.Singleton

import Toolkit.Data.Location
import Toolkit.AST

import public Data.Vect
import public Data.Vect.Quantifiers

import Capable.Types
import Capable.Raw.AST
import Capable.Raw.Role
import Capable.Raw.Types
import Capable.Raw.Exprs
import Capable.Raw.Funcs
import Capable.Raw.Protocols

%default total

%hide fields

mutual
  public export
  data Offer : (s : AST OFFER) -> Type where
    O : (fc : FileContext)
     -> (t,s  : String)
     -> (c    : Expr sc)
             -> Offer (Branch (OFFER t s) fc [sc])

  public export
  data Expr : (s : Raw.AST.EXPRSESH) -> Type
    where
      Seq : (fc : FileContext)
         -> Expr this
         -> Expr that
         -> Expr (Branch (SEQ_SESH) fc [this, that])

      -- ## Bindings
      Hole : (ref : Ref)
          -> (prf : AsRef s fc ref)
                 -> Expr (Branch (HOLE_SESH s) fc Nil)

      LetTy : (fc : FileContext)
           -> (s   : String)
           -> (st    : Stored)
           -> (ty    : Ty t)
           -> (val   : Expr v)
           -> (scope : Expr body)
                    -> Expr (Branch (LETTY_SESH st s) fc [t,v,body])

      Let   : (fc : FileContext)
           -> (s   : String)
           -> (st    : Stored)
           -> (val   : Expr v)
           -> (scope : Expr body)
                    -> Expr (Branch (LET_SESH st s) fc [v,body])

      LetRec : (fc    : FileContext)
            -> (s     : String)
            -> (scope : Expr body)
                     -> Expr (Branch (LETREC_SESH s) fc [body])

      Call : (fc : FileContext)
          -> (s  : String)
                -> Expr (Branch (CALL_SESH s) fc Nil)

      Split : (fc    : FileContext)
           -> (ss    : List String)
           -> (val   : Expr v)
           -> (scope : Expr body)
                    -> Expr (Branch (SPLIT_SESH ss) fc [v,body])

      -- ## Endpunts
      Crash : (fc   : FileContext)
           -> (expr : Expr val)
                   -> Expr (Branch (CRASH_SESH) fc [val])

      End : (fc   : FileContext)
         -> (expr : Expr val)
                 -> Expr (Branch (END_SESH) fc [val])

      -- ## Channel Operations
      Read : (fc   : FileContext)
          -> (role : Role r)
          -> (prf  : AsVect os offers')
          -> (offs : All Offer offers')
          -> (onEr : Expr err)
                  -> Expr (Branch READ fc (r::err::os))

      Send : (fc : FileContext)
          -> (role : Role r)
          -> (msg  : Expr payload)
          -> (body : Expr rest)
          -> (exc  : Expr except)
                  -> Expr (Branch SEND fc [r, payload, rest, except])

public export
data Session : (raw : AST SESH) -> Type where
  Sesh : (fc    : FileContext)
      -> (prin : Role princ)
      -> (ref   : Ref)
      -> (p     : AsRef prot fc ref)
      -> (prf   : AsVect as az)
      -> (args  : All Arg az)
      -> (ret   : Ty rty)
      -> (scope : Expr body)
               -> Session (Branch (SESH prot)
                                  fc
                                  [ princ
                                  , Branch ARGS fc' as
                                  , rty
                                  , body
                                  ])

mutual

  toOffer : (s : AST OFFER) -> Offer s
  toOffer (Branch (OFFER label name) fc [scope])
    = O fc label name (toExpr scope)

  toOffers : (ss : Vect n (AST OFFER)) -> All Offer ss
  toOffers []
    = []
  toOffers (x :: xs)
    = toOffer x :: toOffers xs

  toExpr : (e : Raw.AST.EXPRSESH) -> Expr e
  toExpr (Branch SEQ_SESH fc [l,r])
    = Seq fc (toExpr l)
             (toExpr r)

  toExpr (Branch (HOLE_SESH str) fc [])
    = Hole (MkRef fc str) R

  toExpr (Branch (LETTY_SESH how_stored real_name) fc [ty,v,s])
    = LetTy fc
            real_name
            how_stored
            (toType ty)
            (toExpr v)
            (toExpr s)

  toExpr (Branch (LET_SESH how_stored real_name) fc [v,s])
    = Let fc real_name how_stored (toExpr v) (toExpr s)

  toExpr (Branch (LETREC_SESH real_name) fc [s])
    = LetRec fc real_name (toExpr s)

  toExpr (Branch (CALL_SESH real_name) fc [])
    = Call fc real_name

  toExpr (Branch (SPLIT_SESH ss) fc [v,body])
    = Split fc ss (toExpr v) (toExpr body)

  toExpr (Branch CRASH_SESH fc [a])
    = Crash fc (toExpr a)

  toExpr (Branch END_SESH fc [a])
    = End fc (toExpr a)

  toExpr (Branch READ fc (r :: err :: os))
    = let (os ** prf) = asVect os
      in Read fc (toRole r) prf (assert_total $ toOffers os) (toExpr err)

  toExpr (Branch SEND fc [r, val,scope,err])
    = Send fc (toRole r)
              (toExpr val)
              (toExpr scope)
              (toExpr err)


export
toSession : (e : AST SESH) -> Session e
toSession (Branch (SESH a) fc [p,Branch ARGS _ as,c,d])
  = let (az ** prf) = asVect as
    in Sesh fc (toRole p)
               (MkRef fc a)
               R
               prf
               (toArgs az)
               (toType c)
               (toExpr d)

-- [ EOF ]
