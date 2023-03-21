||| Bespoke data types to capture results of execution.
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Capable.Exec.Results

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
import Capable.Exec.IPC

%default total
%hide type

namespace Expr
  public export
  data Result : (store : List Ty.Base) -> (type : Ty.Base) -> Type where
    Value : {new   : List Ty.Base}
         -> (store : Heap new)
         -> (value : Value new type)
         -> (prf   : Subset old new)
                  -> Result old type

  namespace NoChange
    export
    return : {store : List Ty.Base}
          -> (heap  : Heap store)
          -> (value : Value store type)
                   -> Capable (Result store type)
    return heap value = pure (Value heap value (noChange _))

  namespace Changed
    export
    return : {store,store' : List Ty.Base}
          -> (prf          : Subset store store')
          -> (res          : Result       store' type)
                          -> Capable (Result store   type)

    return prf (Value h val p)
      = pure (Value h val (trans prf p))

    export
    return2 : {store,store',store'' : List Ty.Base}
           -> (p1   : Subset store  store')
           -> (p2   : Subset        store' store'')
           -> (rest : Result store'' b)
                   -> Capable (Result store b)
    return2 p1 p2 rest
      = do res <- return p2 rest
           return p1 res

namespace Args

  public export
  data Results : (store : List Ty.Base)
              -> (types : List Ty.Base)
                       -> Type
    where
      Args : {new   : List Ty.Base}
          -> (store : Heap  new)
          -> (args  : DList Ty.Base (Value new) types)
          -> (prf   : Subset  old new )
                   -> Results old types

namespace Fields

  public export
  data Results : (store : List Ty.Base)
              -> (types : List (String,Ty.Base))
                       -> Type
    where
      Fields : {new   : List Ty.Base}
            -> (store : Heap  new)
            -> (args  : DList (String,Ty.Base) (Field new) types)
            -> (prf   : Subset  old new )
                     -> Results old types
namespace ArgsV

  public export
  data Results : (store : List Ty.Base)
              -> (types : Vect n Ty.Base)
                       -> Type
    where
      Args : {new   : List Ty.Base}
          -> (store : Heap  new)
          -> (args  : DVect Ty.Base (Value new) n types)
          -> (prf   : Subset  old new )
                   -> Results old types

namespace Session
  namespace Exprs
    public export
    data Result : (roles : List Ty.Role) -> (store : List Ty.Base) -> (type : Ty.Base) -> Type where
      Value : {new   : List Ty.Base}
           -> (store : Heap new)
           -> (chans : Channels roles)
           -> (value : Value new type)
           -> (prf   : Subset old new)
                    -> Result roles old type

namespace Assigns
  public export
  data Result : (store : List Ty.Base)

             -> (roles : List Ty.Role)
             -> (prin  : Roles roles ss)
             -> Type where
    Value : {new   : List Ty.Base}
         -> (store : Heap new)
         -> (as    : Assignments roles new ps)
         -> (prf   : Subset old new)
                  -> Result old roles ps

-- [ EOF ]
