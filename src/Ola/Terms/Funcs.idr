||| Functions are perhaps recursive
|||
||| Module    : Funcs.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
module Ola.Terms.Funcs

import Data.List.Elem
import Data.Vect

import Ola.Terms.Types
import Ola.Terms.Vars
import Ola.Terms.Exprs
import Ola.Terms.Stmts

%default total

public export
data Func : (types : List Ty)
         -> (stack : List Ty)
         -> (type  : Ty)
                  -> Type
  where
    ||| A non-recusrive function.
    Fun : {arg,return:Ty}
       -> (body : Stmt types (arg::stack)           return)
       ->         Func types stack (FUNC arg return)

    ||| A recursive function
    ||| This might be a rather dodgy way to do it...
    ||| We shall see...
    Rec : (func : Stmt types (arg :: stack) return)
               -> Func types         stack  (FUNC arg return)


-- [ EOF ]
