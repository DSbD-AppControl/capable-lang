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
        -> (ds    : List Ty.Base)
        -> (ss    : List Ty.Session)
        -> (gs    : List Ty.Method)
        -> (ls    : List Ty.Base)
        -> (type  : Base)
                  -> Type
  where
    T : (ty   : Ty      ds          type )
     -> (e    : Expr rs ds ss gs ls type)
             -> The  rs ds ss gs ls type

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
  data HoleContext
    = H (Context Ty.Method gs)
        (Context Ty.Base   ls)

  public export
  record Env (rs : List Ty.Role)
             (ds : List Ty.Base)
             (ss : List Ty.Session)
             (gs : List Ty.Method)
             (ls : List Ty.Base)
    where
      constructor E
      rho    : Context Ty.Role    rs
      delta  : Context Ty.Base    ds
      sigma  : Context Ty.Session ss
      gamma  : Context Ty.Method  gs
      lambda : Context Ty.Base    ls
      mu     : SortedMap String HoleContext

  export
  empty : Env Nil Nil Nil Nil Nil
  empty = E   Nil Nil Nil Nil Nil empty

  namespace Mu
    export
    extend : (env : Env rs ds ss gs ls)
          -> (s   : String)
                 -> Env rs ds ss gs ls
    extend env s
      = { mu $= insert s (H (gamma env) (lambda env))} env

  namespace Rho
    export
    extend : (env : Env rs ds ss gs ls)
          -> (s   : String)
                 -> Env (MkRole::rs) ds ss gs ls
    extend env s
      = { rho $= (::) (I s MkRole)} env

  namespace Gamma
    export
    extend : (env : Env rs ds ss gs ls)
          -> (s   : String)
          -> (ty  : Method)
                 -> Env rs ds ss (ty::gs) ls
    extend env s ty
      = { gamma $= (::) (I s ty) } env

    export
    lookup : {gs    : _}
          -> (ctxt  : Env rs ds ss gs ls)
          -> (s     : Ref)
                   -> Capable (DPair Ty.Method (IsVar gs))
    lookup env ref
      = Common.lookup (gamma env) ref

  namespace Sigma
    export
    extend : (env : Env rs ds ss gs ls)
          -> (s   : String)
          -> (ty  : Session)
                 -> Env rs ds (ty::ss) gs ls
    extend env s ty
      = { sigma $= (::) (I s ty) } env

    export
    lookup : {ss    : _}
          -> (ctxt  : Env rs ds ss gs ls)
          -> (s     : Ref)
                   -> Capable (DPair Ty.Session (IsVar ss))
    lookup env ref
      = Common.lookup (sigma env) ref

  namespace Lambda
    export
    extend : (env : Env rs ds ss gs ls)
          -> (s   : String)
          -> (ty  : Base)
                 -> Env rs ds ss gs (ty::ls)
    extend env s ty
      = { lambda $= (::) (I s ty) } env

    export
    lookup : {ls    : _}
          -> (ctxt  : Env rs ds ss gs ls)
          -> (s     : Ref)
                   -> Capable (DPair Ty.Base (IsVar ls))
    lookup env ref
      = Common.lookup (lambda env) ref

--  public export
--  data EnvLookup : (gs : List Ty.Method)
--                -> (ls : List Ty.Base)
--                -> Ty.Base -> Type
--    where
--      IsLocal  : IsVar ls type -> EnvLookup gs ls type
--      IsGlobal : IsVar gs type -> EnvLookup gs ls type
--
--  export
--  lookup : {gs,ls : _}
--        -> (ctxt  : Env rs ds ss gs ls)
--        -> (s     : Ref)
--                 -> Capable (DPair Ty.Base (EnvLookup gs ls))
--  lookup env ref
--    = tryCatch (do (ty ** idx) <- Common.lookup (gamma env) ref
--                   pure (_ ** IsGlobal idx))
--
--               (\err => do (ty ** idx) <- Common.lookup (lambda env) ref
--                           pure (_ ** IsLocal idx))


prettyCtxt : Pretty a => Context a ls -> List (Doc ann) -> List (Doc ann)
prettyCtxt [] acc = acc
prettyCtxt ((I name x) :: rest) acc
  = prettyCtxt rest (acc ++ [(hsep [pretty name, colon, pretty x])])

export
showHoleExit : Context Ty.Base ls
            -> String
            -> Base
            -> Capable e
showHoleExit g n t
    = do putStrLn "Showing first available hole."
         putStrLn "Need to collect them..."
         let pc = prettyHole g n t
         putStrLn $ (show . annotate ()) pc
         exitSuccess

    where
      prettyHole : Context Ty.Base ls
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
showHoleSessionExit : Context Ty.Base ls
                   -> Context Ty.Role rs
                   -> Context Protocol.Kind ks
                   -> Local ks rs
                   -> String
                   -> Capable e
showHoleSessionExit g r k t x
  = do putStrLn "Showing first available hole."
       putStrLn "Need to collect them..."
       putStrLn "## Typing Context"
       putStrLn $ (show . annotate ()) (vcat $ prettyCtxt g Nil)
       putStrLn "## Recursion Vars"
       printLn  $ keys k
       putStrLn "## Roles"
       printLn $ keys r
       putStrLn "---"
       putStrLn "\{x} : TODO"
       exitSuccess
-- [ EOF ]
