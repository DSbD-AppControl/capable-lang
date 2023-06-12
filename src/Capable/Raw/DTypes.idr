||| Views on DataTypes.
|||
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Capable.Raw.DTypes

import Data.Vect

import Toolkit.Data.DVect

import Toolkit.Data.Location

import Capable.Types
import Capable.Raw.AST
import Capable.Raw.Types

%default total
%hide type
%hide fields

namespace Named
  public export
  data Args : (rs : Vect n Raw.AST.FIELD)
                 -> Type
    where

      Nil : Args Nil

      Add : {r , rs : _}
         -> (fc   : FileContext)
          -> (s    : String)
          -> (ty   : Ty   r)
          -> (rest : Named.Args rs)
                  -> Named.Args (Branch (FIELD s) fc [r] :: rs)


public export
data DTy : Raw.AST.DTYPE -> Type
  where

    TyData : {  fields' : Vect (S n) Raw.AST.FIELD}
          -> (fc  : FileContext)
          -> (k   : DKind)
          -> (prf : AsVect fields fields')
          -> (fs  : Args fields')
                 -> DTy (Branch (DTYPE k) fc fields)


toFields : (rs : Vect n Raw.AST.FIELD)
              -> Args rs
toFields []
  = []
toFields (Branch (FIELD s) fc [x]::xs)
  = Add fc s (toType x) (toFields xs)

export
toDType : (r : Raw.AST.DTYPE)
            -> DTy r
toDType (Branch (DTYPE k) fc fs)
  = let (vs ** prf) = asVect fs
    in TyData fc
              k
              prf
              (assert_total $ toFields vs)


-- [ EOF ]
