||| Non recursive function bodies.
|||
||| @TODO make recursive with a recursive type...
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Capable.Terms.Funcs

import Data.List.Elem
import Data.Vect

import Capable.Terms.Types
import Capable.Terms.Vars
import Capable.Terms.Exprs
import Capable.Terms.Sessions

%default total

public export
data Func : (roles : List Ty.Role)
         -> (types : List Ty.Base)
         -> (sesh  : List Ty.Session)
         -> (stack : List Ty.Method)
         -> (type  :      Ty.Method)
                  -> Type
  where
    ||| A non-recusive. function.
    Fun : {args   : List Ty.Base}
       -> {return : Ty.Base}
       -> (body   : Expr roles types ss stack       args return)
                 -> Func roles types ss stack (FUNC args return)

-- [ EOF ]
