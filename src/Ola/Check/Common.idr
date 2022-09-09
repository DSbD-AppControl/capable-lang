|||
||| Module    : Common.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
module Ola.Check.Common

import public Decidable.Equality
import public Data.Singleton
import public Data.Fin

import public Toolkit.Decidable.Informative
import public Toolkit.Data.Location

import public Toolkit.Data.List.AtIndex
import public Toolkit.DeBruijn.Context
import public Toolkit.DeBruijn.Context.Item
import public Toolkit.DeBruijn.Renaming

import Data.List.Elem

import Ola.Core
import Ola.Types
import Ola.Terms.Types
import Ola.Terms.Exprs

throw : Typing.Error -> Ola a
throw = (throw . TyCheck . E)

export
throwAt : FileContext -> Typing.Error -> Ola a
throwAt l e = throw $ TyCheck (S l (E e))

export
unknown : FileContext -> Ola a
unknown fc = Common.throwAt fc Unknown

export
mismatch : (g,e : Types.Ty) -> Ola a
mismatch g e = Common.throw $ Mismatch g e

export
notBound : Ref -> Ola a
notBound r = throw (NotBound r)

export
mismatchAt : (fc : FileContext) -> (g,e : Types.Ty) -> Ola a
mismatchAt fc g e = throwAt fc (Mismatch g e)

namespace Maybe
  export
  embedAt : FileContext
         -> Typing.Error
         -> Maybe a
         -> Ola   a
  embedAt _ _ (Just prf)
    = pure prf
  embedAt fc err Nothing
    = throwAt fc err

namespace Decidable
  export
  embedAt : FileContext
         -> Typing.Error
         -> Dec     a
         -> Ola a
  embedAt _ _ (Yes prf)
    = pure prf
  embedAt fc err (No _)
    = throwAt fc err

  namespace Informative
    export
    embedAt : FileContext
           -> Typing.Error
           -> DecInfo e a
           -> Ola   a
    embedAt _ _ (Yes prfWhy)
      = pure prfWhy
    embedAt fc err (No _ _)
      = throwAt fc err

    export
    embedAtInfo : FileContext
               -> Typing.Error
               -> DecInfo e a
               -> Ola   a
    embedAtInfo = embedAt

export
compare : (fc  : FileContext)
       -> (a,b : Types.Ty)
              -> Ola (a = b)
compare fc a b
  = embedAt fc (Mismatch a b)
               (decEq    a b)

public export
data The : (ds,gs : List Types.Ty)
                 -> Type
  where
    T : (type : Types.Ty)
     -> (ty   : Ty   ds    type )
     -> (e    : Expr ds gs type)
             -> The  ds gs
-- [ EOF ]
