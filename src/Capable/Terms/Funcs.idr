||| Functions/methods/procedures...
|||
||| Module    : Funcs.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
module Capable.Terms.Funcs

import Data.List.Elem
import Data.Vect

import Capable.Terms.Types
import Capable.Terms.Vars
import Capable.Terms.Exprs

%default total

public export
data Func : (roles : List Ty.Role)
         -> (types : List Ty.Base)
         -> (stack : List Ty.Base)
         -> (type  :      Ty.Base)
                  -> Type
  where
    ||| A non-recusive. function.
    Fun : {args   : List Ty.Base}
       -> {return : Ty.Base}
       -> (body   : Expr roles types (args ++ stack) return)
                 -> Func roles types stack (FUNC args return)

-- [ EOF ]
