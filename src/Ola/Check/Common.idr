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

%default total
%hide type

throw : Typing.Error -> Ola a
throw = (throw . TyCheck . E)

export
throwAt : FileContext -> Typing.Error -> Ola a
throwAt l e = throw $ TyCheck (S l (E e))

export
unknown : FileContext -> Ola a
unknown fc = Common.throwAt fc Unknown

export
mismatch : (g,e : Ty.Base) -> Ola a
mismatch g e = Common.throw $ Mismatch g e

export
notBound : Ref -> Ola a
notBound r = throw (NotBound r)

export
mismatchAt : (fc : FileContext) -> (g,e : Ty.Base) -> Ola a
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
       -> (a,b : Ty.Base)
              -> Ola (a = b)
compare fc a b
  = embedAt fc (Mismatch a b)
               (decEq    a b)

public export
data The : (rs    : List Ty.Role)
        -> (ds,gs : List Ty.Base)
        -> (type  : Base)
                 -> Type
  where
    T : (ty   : Ty      ds    type )
     -> (e    : Expr rs ds gs type)
             -> The  rs ds gs type

export
lookup : {type, types : _}
      -> (ctxt  : Context type types)
      -> (s     : Ref)
               -> Ola (DPair type (IsVar types))
lookup ctxt s
  = do prf <- embedAtInfo
                (span s)
                (NotBound s)
                (Lookup.lookup (get s) ctxt)
       let (r ** loc ** prfN) = deBruijn prf
       pure (r ** V loc prfN)

export
exists : {type, types : _}
      -> (fc : FileContext)
      -> (ctxt : Context type types)
      -> String
              -> Ola ()
exists fc ctxt s
  = case Lookup.lookup s ctxt of
      No _ _ => pure ()
      Yes _ => throwAt fc (AlreadyBound (MkRef fc s))


namespace Env
  public export
  record Env (rs : List Ty.Role)
             (ds,gs : List Ty.Base)
    where
      constructor E
      rho   : Context Ty.Role rs
      delta : Context Ty.Base ds
      gamma : Context Ty.Base gs


  export
  empty : Env Nil Nil Nil
  empty = E Nil Nil Nil

  namespace Rho
    export
    extend : (env : Env rs ds gs)
          -> (s   : String)
                 -> Env (MkRole::rs) ds gs
    extend (E rho delta gamma) s
      = E (I s MkRole :: rho) delta gamma

  namespace Gamma
    export
    extend : (env : Env rs ds gs)
          -> (s   : String)
          -> (ty  : Base)
                 -> Env rs ds (ty::gs)
    extend (E rho delta gamma) s ty
      = E rho delta (I s ty :: gamma)

-- [ EOF ]
