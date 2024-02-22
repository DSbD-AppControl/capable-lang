||| Pretty Print Capable Programs.
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Capable.Terms.Pretty

import Data.Maybe
import Data.Vect
import Data.String
import Data.List.Elem
import Data.List1.Elem
import Data.List.Quantifiers
import Data.Vect.Quantifiers

import System.File
import System.Escape

import public Text.PrettyPrint.Prettyprinter
import Text.PrettyPrint.Prettyprinter.Render.String


import Toolkit.Data.Vect.Extra
import Toolkit.Data.DList
import Toolkit.Data.DVect

import Capable.Core

import Capable.Types

import Capable.Terms
%default total

export
session : {ks : _} -> {t : Local ks rs}
         -> (kctxt : Context Kind    ks)
         -> (rctxt : Context Ty.Role rs)
         -> (expr  : Expr rs
                          roles -- globla roles
                          types -- bound types
                          prots -- protocol
                          stac_f
                          stac_l
                          ks
                          whom
                          t
                          UNIT)
        -> Doc ()
session kctxt rctxt (Hole str)
  = pretty "?" <+> pretty str
session kctxt rctxt (Seq x y)
  = pretty "?skippingSeq"
session kctxt rctxt (Let ty expr rest)
  = pretty "?skippingLet"
session kctxt rctxt (Split expr rest)
  = pretty "?skippingSPlit"
session kctxt rctxt (Cond cond tt ff prf)
  = pretty "?skippingCond"
session kctxt rctxt (Match expr cases prf)
  = pretty "?skippingCond"

session kctxt rctxt (LetRec {e=R a} x)
  = pretty "loop" <+> parens (pretty a) <+> braces (session (extend kctxt a (R a)) rctxt x)
session kctxt rctxt (Call x)
  = pretty "call" <+> parens (pretty $ reflect kctxt x)

session kctxt rctxt (Crash (Hole x))
  = pretty "crash" <+> parens (pretty x)
session kctxt rctxt (Crash _)
  = pretty "crash" <+> (parens $ pretty "?hole")
session kctxt rctxt (End (Hole x))
  = pretty "crash" <+> parens (pretty x)
session kctxt rctxt (End _)
    = pretty "crash" <+> parens (pretty "?hole")

session kctxt rctxt (Read from prf offers onErr)
  = pretty "recv" <+> brackets (pretty $ reflect rctxt from) <+> braces (pretty "todo")

session kctxt rctxt (Send toWhom label payload mprf rest onErr)
  = pretty "?send"


-- [ EOF ]
