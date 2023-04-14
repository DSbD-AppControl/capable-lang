module Capable.Types.Protocol.Local.Synth

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

import public Capable.Types.Protocol.Common

%default total

public export
data Local : List Kind -> List Role -> Type where
  Crash : Local ks rs
  End : Local ks rs
  Call : {vs : _} -> RecVar vs -> Local vs rs
  Rec : Local (R::vs) rs -> Local vs rs
  Select : {rs,ks : _}
        -> (whom  : Role rs)
        -> (label : String)
        -> (type  : Base)
        -> (prf   : Marshable type)
        -> (cont  : Local ks rs)
                 -> Local ks rs

  Offer : {rs,ks   : _}
       -> (whom    : Role rs)
       -> (type    : Singleton (UNION (field:::fs)))
       -> (prfM    : Marshable (UNION (field:::fs)))
       -> (choices : DList (String,Base)
                            (Branch Local ks rs)
                            (field::fs))
                  -> Local ks rs


public export
Branches : List Kind -> List Role -> List (String, Base)-> Type
Branches ks rs
  = DList (String, Base)
          (Branch Local ks rs)

namespace Closed
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
            -> Synth.Branches ks rs ls
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

    pretty acc kctxt rctxt (Select whom l t _ k)
      = group
      $ parens
      $ hsep
      [ pretty "selects from"
      , pretty (reflect rctxt whom)
      , pretty l
      , parens (pretty t)
      , pretty "."
      , indent 2 (pretty acc kctxt rctxt k)
      ]

    pretty acc kctxt rctxt (Offer whom (Val (UNION (f:::fs))) _ cs)

      = group
      $ parens
      $ hsep
      [ pretty "offers to"
      , pretty (reflect rctxt whom)
      , pretty (show (UNION (f:::fs)))
      , hang 2 (branches acc kctxt rctxt cs) ]

  export
  toString : (rctxt : Context Ty.Role rs)
          -> (ltype : Local Nil rs)
                   -> String
  toString r l = show (pretty Z Nil r l)


  namespace Open

    export
    toString : (kctxt : Context Kind ks)
            -> (rctxt : Context Ty.Role rs)
            -> (ltype : Local ks rs)
                     -> String
    toString ks r l = show (pretty  Z ks r l)

-- [ EOF ]
