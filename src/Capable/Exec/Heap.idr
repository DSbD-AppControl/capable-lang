||| An API for heap operations.
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Capable.Exec.Heap

import Data.Maybe
import Data.Vect
import Data.String
import Data.List.Elem
import Data.List1.Elem
import Data.List.Quantifiers

import System.File

import Toolkit.Data.Vect.Extra
import Toolkit.Data.DList
import Toolkit.Data.DVect

import Capable.Core
import Capable.Terms

import Capable.Values
import Capable.Values.Marshall

import Capable.Exec.Env
import Capable.Exec.Common
import Capable.Exec.Results


%default total
%hide type

export
insert : {store : List Ty.Base}
      -> {type  : Ty.Base}
      -> (value : Value store type)
      -> (heap  : Heap  store)
               -> Capable (Expr.Result store (REF type))
insert {store} {type} v h
  = let new = snoc_add type store              -- Extend type-level context
    in let v' = Address (snoc_elem store type) -- Generate address
    in let h' = snoc (map (weaken new) h)      -- Update heap
                     (weaken new v)
    in pure (Value h' v' new)

export
fetch : {store : List Ty.Base}
     -> (loc   : IsVar  store type)
     -> (heap  : Heap store)
              -> Capable (Expr.Result store type)
fetch loc heap
  = let val = Heap.lookup loc heap
    in return heap val


export
mutate : {store : List Ty.Base}
      -> (loc   : IsVar store type)
      -> (heap  : Heap store)
      -> (val   : Val type store)
               -> Capable (Expr.Result store UNIT)

mutate loc heap val
  = let new_heap = Heap.replace loc val heap
    in return new_heap U


-- [ EOF ]
