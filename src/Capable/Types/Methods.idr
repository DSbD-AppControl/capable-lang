|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Capable.Types.Methods

import Decidable.Equality
import Data.String

import public Data.Singleton

import Data.List.Elem
import Data.List1
import Data.List.Quantifiers

import Text.PrettyPrint.Prettyprinter

import Toolkit.Decidable.Do

import public Toolkit.Decidable.Informative
import public Toolkit.Decidable.Equality.Indexed

import Toolkit.Data.List.Quantifiers

import public Toolkit.Data.DList
import Toolkit.Data.DList.All

import public Toolkit.DeBruijn.Renaming

import Capable.Bootstrap
import Capable.Types.Role
import Capable.Types.Base
import Capable.Types.Protocol

%default total

namespace Ty
  public export
  data Method : Type where
    FUNC : (args : List Base) -> (ret : Base) -> Method

    SESH : (ctxt : Context Role rs)
        -> (whom : Role rs)
        -> (prot : Local Nil rs)
        -> (args : List Base)
        -> (ret  : Base)
                -> Method

{- [ NOTE ]

DecEq is hard because of the implicit variables in SESH.

Technically we should not need it...but you never know...

-}

method : Method -> Doc ann
method (SESH ctxt w p as r) = pretty "(TODO Sesh)"
method (FUNC xs x)
  = group
  $ parens
  $ hsep
  $ punctuate (pretty "->")
  $ assert_total
  $ map pretty
  $ (xs ++ [x])

export
Pretty Method where
  pretty = method

export
Show Method where
  show = (show . annotate () . pretty)

-- [ EOF ]
