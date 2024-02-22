||| Shared utilities for elaboration.
|||
||| Copyright : COPYRIGHT
||| License   : see LICENSE
|||
module Capable.Check.Common

import public Decidable.Equality
import public Data.Singleton
import public Data.Fin
import        Data.String
import        Text.PrettyPrint.Prettyprinter

import        Data.SortedMap

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

namespace Either
  export
  embedAt : FileContext
         -> (e -> Typing.Error)
         -> Either e a
         -> Capable  a
  embedAt _ _ (Right prf)
    = pure prf
  embedAt fc err (Left e)
    = throwAt fc (err e)

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

    namespace Error
      export
      embedAt : FileContext
             -> (e -> Typing.Error)
             -> DecInfo e a
             -> Capable   a
      embedAt _ _ (Yes p) = pure p
      embedAt fc e (No msg _) = throwAt fc (e msg)

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
                 -> Env (MkRole s::rs) ds ss gs ls
    extend env s
      = { rho $= (::) (I s (MkRole s))} env

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

prettyCtxt : Pretty a => Context a ls -> List (Doc ann) -> List (Doc ann)
prettyCtxt [] acc = acc
prettyCtxt ((I name x) :: rest) acc
  = prettyCtxt rest (acc ++ [(hsep [pretty name, colon, pretty x])])

export
showHole : Context Ty.Base ls
        -> String
        -> Base
        -> Capable ()
showHole g n t
    = do let pc = prettyHole g n t
         putStrLn $ (show pc)


    where
      prettyHole : Context Ty.Base ls
                -> String
                -> Base
                -> Doc ()
      prettyHole x str y
        = vsep
        $ [ vcat
           $ prettyCtxt x Nil
           ++ [ pretty "---"
              , group
              $ hsep
              [ pretty str
              , colon
              , pretty y]
              ]
          ]

export
showHoleSession : Context Ty.Base ls
               -> Context Ty.Role rs
               -> Context Protocol.Kind ks
               -> Local.Local ks rs
               -> String
               -> Capable ()
showHoleSession g r k t x
  = putStrLn (show prettyThings)


  where prettyGamma : List (Doc ())
        prettyGamma
          = case g of
              Nil => []
              (_::_) =>
                  [ pretty "## Typing Context"
                  , vcat
                    $ prettyCtxt g Nil
                  ]

        prettyList : String -> List String -> List (Doc ())
        prettyList _ Nil
          = Nil
        prettyList t (x::xs)
          = [ hsep [pretty "## ", pretty t]
            , vsep $ map (\k => pretty "+ \{k}") (x::xs)
            ]

        prettyThings : Doc ()
        prettyThings
          = vsep
            $  prettyGamma
            ++ prettyList "Recursion Vars" (keys k)
            ++ prettyList "Roles" (keys r)
            ++ [ pretty "---"
               , hsep [ pretty x, colon, pretty k r t]
               ]

-- [ EOF ]
