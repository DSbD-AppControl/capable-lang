module Capable.Pretty

import Data.Singleton
import Data.String

import Text.PrettyPrint.Prettyprinter

import Capable.Core
import Capable.Check.Common

--import Capable.Check

import Capable.Terms
import Capable.Terms.Protocols.Projection
import Capable.State

%default total

reflect : (ctxt  : Context a rs)
       -> (loc   : IsVar rs l)
                -> String
reflect [] (V _ Here) impossible
reflect [] (V _ (There later)) impossible

reflect ((I name x) :: rest) (V 0 prf) = name
reflect (elem :: rest) (V (S k) (There later)) = reflect rest (V k later)

showAcc : Nat -> String
showAcc n
  = if lt n 26
         then singleton (chr (cast (plus 97 n)))
         else (singleton (chr (cast (plus 97 (mod n 26))))) <+> (assert_total $ showAcc  (minus n 26))

mutual
  branch : (acc : Nat)
        -> (kctxt : Context Kind ks)
        -> (rctxt : Context Ty.Role rs)
        -> Branch Local ks rs l
        -> Doc ()
  branch acc kctxt rctxt (B label type c)
    = group
    $ align
    $ vcat
    [ pretty label <+> parens (pretty (show type))
    , pretty "." <+> pretty acc kctxt rctxt c
    ]

  choices : List (Doc ann) -> Doc ann
  choices = group . encloseSep (flatAlt (pretty "[ ") (pretty "["))
                               (flatAlt (pretty "]") (pretty "]"))
                               (flatAlt (pretty "| ") (pretty " | "))
  branches : (acc : Nat)
          -> (kctxt : Context Kind ks)
          -> (rctxt : Context Ty.Role rs)
          -> Local.Branches ks rs ls
          -> Doc ()
  branches acc kctxt rctxt xs
    =  let prettyXS = mapToList (branch acc kctxt rctxt) xs
    in assert_total
    $ choices prettyXS

  pretty : (acc : Nat)
        -> (kctxt : Context Kind ks)
        -> (rctxt : Context Ty.Role rs)
        -> (ltype : Local ks rs)
                 -> Doc ()
  pretty _ _ _ Crash
    = pretty "Crash"

  pretty _ _ _ End
    = pretty "End"

  pretty acc kctxt rctxt (Call x)
    = group
    $ parens (hsep [pretty "Call", pretty (reflect kctxt x)])

  pretty acc kctxt rctxt (Rec x)
    = let v    = showAcc acc in
      let cont = pretty (S acc) (extend kctxt v R) rctxt x
      in group
      $  align
      $  vsep [ group (pretty "rec" <+> parens (pretty v) <+> pretty ".")
              , indent 2 cont]

  pretty acc kctxt rctxt (Choice BRANCH whom (Val (UNION (f:::fs))) _ cs)
    = group
    $ parens
    $ hsep
    [ pretty "offers to"
    , pretty (reflect rctxt whom)
    , pretty (show (UNION (f:::fs)))
    , hang 2 (branches acc kctxt rctxt cs) ]


  pretty acc kctxt rctxt (Choice SELECT whom (Val (UNION (f:::fs))) _ cs)
    = group
    $ parens
    $ hsep
    [ pretty "selects from"
    , pretty (reflect rctxt whom)
    , pretty (show (UNION (f:::fs)))
    , hang 2 (branches acc kctxt rctxt cs) ]

export
toString : (rctxt : Context Ty.Role rs)
        -> (ltype : Local Nil rs)
                 -> String
toString r l = show (pretty Z Nil r l)

-- [ EOF ]
