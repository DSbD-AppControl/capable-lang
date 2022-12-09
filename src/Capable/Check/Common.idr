|||
||| Module    : Common.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
module Capable.Check.Common

import public Decidable.Equality
import public Data.Singleton
import public Data.Fin

import Text.PrettyPrint.Prettyprinter

import Data.SortedMap

import public Toolkit.Decidable.Informative
import public Toolkit.Data.Location

import public Toolkit.Data.List.AtIndex
import public Toolkit.DeBruijn.Context
import public Toolkit.DeBruijn.Context.Item
import public Toolkit.DeBruijn.Renaming

import Data.List.Elem

import Capable.Core
import Capable.Types
import Capable.Terms.Types
import Capable.Terms.Exprs

%default total
%hide type

throw : Typing.Error -> Capable a
throw = (throw . TyCheck . E)

export
throwAt : FileContext -> Typing.Error -> Capable a
throwAt l e = throw $ TyCheck (S l (E e))

export
unknown : FileContext -> Capable a
unknown fc = Common.throwAt fc Unknown

export
mismatch : (g,e : Ty.Base) -> Capable a
mismatch g e = Common.throw $ Mismatch g e

export
notBound : Ref -> Capable a
notBound r = throw (NotBound r)

export
mismatchAt : (fc : FileContext) -> (g,e : Ty.Base) -> Capable a
mismatchAt fc g e = throwAt fc (Mismatch g e)

namespace Maybe
  export
  embedAt : FileContext
         -> Typing.Error
         -> Maybe a
         -> Capable   a
  embedAt _ _ (Just prf)
    = pure prf
  embedAt fc err Nothing
    = throwAt fc err

namespace Decidable
  export
  embedAt : FileContext
         -> Typing.Error
         -> Dec     a
         -> Capable a
  embedAt _ _ (Yes prf)
    = pure prf
  embedAt fc err (No _)
    = throwAt fc err

  namespace Informative

    export
    embedAt : FileContext
           -> Typing.Error
           -> DecInfo e a
           -> Capable   a
    embedAt _ _ (Yes prfWhy)
      = pure prfWhy
    embedAt fc err (No _ _)
      = throwAt fc err

    export
    embedAtInfo : FileContext
               -> Typing.Error
               -> DecInfo e a
               -> Capable   a
    embedAtInfo = embedAt

export
compare : (fc  : FileContext)
       -> (a,b : Ty.Base)
              -> Capable (a = b)
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
               -> Capable (DPair type (IsVar types))
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
              -> Capable ()
exists fc ctxt s
  = case Lookup.lookup s ctxt of
      No _ _ => pure ()
      Yes _ => throwAt fc (AlreadyBound (MkRef fc s))


namespace Env
  public export
  data HoleContext = H (Context Ty.Base ms)

  public export
  record Env (rs : List Ty.Role)
             (ds,gs : List Ty.Base)
    where
      constructor E
      rho   : Context Ty.Role rs
      delta : Context Ty.Base ds
      gamma : Context Ty.Base gs
      mu    : SortedMap String HoleContext

  export
  empty : Env Nil Nil Nil
  empty = E Nil Nil Nil empty

  namespace Mu
    export
    extend : (env : Env rs ds gs)
          -> (s   : String)
                 -> Env rs ds gs
    extend env s
      = { mu $= insert s (H (gamma env))} env

  namespace Rho
    export
    extend : (env : Env rs ds gs)
          -> (s   : String)
                 -> Env (MkRole::rs) ds gs
    extend env s
      = { rho $= (::) (I s MkRole)} env

  namespace Gamma
    export
    extend : (env : Env rs ds gs)
          -> (s   : String)
          -> (ty  : Base)
                 -> Env rs ds (ty::gs)
    extend env s ty
      = { gamma $= (::) (I s ty) } env


prettyCtxt : Context Ty.Base gs -> List (Doc ann) -> List (Doc ann)
prettyCtxt [] acc = acc
prettyCtxt ((I name x) :: rest) acc
  = prettyCtxt rest (acc ++ [(hsep [pretty name, colon, pretty x])])

prettyHole : Context Ty.Base gs
          -> String
          -> Base
          -> Doc ann
prettyHole x str y
  = vcat
  $ prettyCtxt x Nil
  ++ [ pretty "---"
     , group
     $ hsep
     [ pretty str
     , colon
     , pretty y]
     ]

export
showHoleExit : Context Ty.Base gs
            -> String
            -> Base
            -> Capable e
showHoleExit g n t
  = do putStrLn "Showing first available hole."
       putStrLn "Need to collect them..."
       let pc = prettyHole g n t
       putStrLn $ (show . annotate ()) pc
       exitSuccess

-- [ EOF ]
