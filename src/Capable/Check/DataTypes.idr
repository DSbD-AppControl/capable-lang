||| Type-checker for datatypes.
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Capable.Check.DataTypes

import Toolkit.Data.Location
import Toolkit.Data.DList
import Toolkit.Data.DVect

import Data.Singleton

import Capable.Types
import Capable.Core

import Capable.Raw.AST
import Capable.Raw.Types
import Capable.Raw.DTypes

import Capable.Check.Common
import Capable.Check.Types

import Capable.Terms.Vars
import Capable.Terms.Types

%default total
%hide type

synthFields : {types : List Ty.Base}
           -> (ctxt  : Context Ty.Base types)
           -> (args  : Named.Args as)
                    -> Capable (DPair (List  (String, Ty.Base))
                                  (DList (String, Ty.Base)
                                         (Ty types . Builtin.snd)
                                         ))
synthFields ctxt []
  = pure (_ ** Nil)

synthFields ctxt (Add fc s ty rest)
  = do (a ** ty) <- Types.synth ctxt ty
       (as ** tys) <- synthFields ctxt rest
       pure ((s,a)::as ** (ty::tys))

export
synth : {types : List Ty.Base}
     -> (ctxt : Context Ty.Base types)
     -> (syn  : DTy t)
             -> Capable (DPair Ty.Base (Ty types))

synth ctxt (TyData fc k prf (Add fc' s x fs))
  = do checkLabels Nil (Add fc' s x fs)

       (_ ** (a::tmF)) <- synthFields ctxt (Add fc' s x fs)
             | _ => throwAt fc Unknown

       case k of
         UNION => pure (_ ** TyUnion (a::tmF))
         STRUCT => pure (_ ** TyRecord (a::tmF))

  where checkLabels : List String -> Named.Args awes -> Capable ()
        checkLabels _ Nil = pure ()
        checkLabels ss (Add fc s _ fs)
          = case isElem s ss of
              No _ => checkLabels (s::ss) fs
              Yes _ => throwAt fc (AlreadyBound (MkRef fc s))

namespace Raw
  export
  synth : {types : List Ty.Base}
       -> (ctxt  : Context Ty.Base types)
       -> (raw   : DTYPE)
                -> Capable (DPair Ty.Base (Ty types))
  synth ctxt r
    = synth ctxt (toDType r)

-- [ EOF ]
