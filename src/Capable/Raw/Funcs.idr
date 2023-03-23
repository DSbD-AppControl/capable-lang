||| A view on Funcs
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
||| Let's be smart about the shape of the tree.
module Capable.Raw.Funcs

import Toolkit.Data.Location
import Toolkit.AST

import Data.Vect.Quantifiers
import Capable.Types
import Capable.Raw.AST
import Capable.Raw.Types
import Capable.Raw.Exprs

%default total

public export
data Arg : (s : Raw.AST.ARG) -> Type
  where
    A : {t : _}
     -> (fc   : FileContext)
     -> (n    : String)
     -> (type : Ty t)
             -> Arg (Branch (ARG n) fc [t])

toArg : (a : Raw.AST.ARG) -> Arg a
toArg (Branch (ARG str) fc [t])
  = A fc str (toType t)

public export
data Fun : (f : Raw.AST.FUNC) -> Type
  where
    Func : {r : _}
        -> {  az   : Vect n Raw.AST.ARG}
        -> (  fc   : FileContext)
        -> (  prf  : AsVect as az)
        -> (  args : All Arg az)
        -> (  ret  : Ty r)
        -> (  scope : Expr body)
                   -> Fun (Branch FUN fc
                                  [ Branch ARGS fc' as
                                  , r
                                  , body
                                  ])

export
toArgs : (as : Vect n Raw.AST.ARG)
            -> All Arg as
toArgs []
  = []
toArgs (x :: xs)
  = toArg x :: toArgs xs

export
toFun : (f : Raw.AST.FUNC)
          -> Fun f
toFun (Branch FUN fc [Branch ARGS _ as,r,b])
  = let (az ** prf) = asVect as
    in Func fc prf (toArgs az)
                   (toType r)
                   (toExpr b)

-- [ EOF ]
