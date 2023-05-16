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


Uninhabited (Synth.Crash = Synth.End) where
  uninhabited Refl impossible

Uninhabited (Synth.Crash = (Synth.Call x)) where
  uninhabited Refl impossible

Uninhabited (Synth.Crash = (Synth.Rec x)) where
  uninhabited Refl impossible

Uninhabited (Synth.Crash = (Synth.Select a b c d e)) where
  uninhabited Refl impossible

Uninhabited (Synth.Crash = (Synth.Offer a b c d)) where
  uninhabited Refl impossible

Uninhabited (Synth.End = (Synth.Call x)) where
  uninhabited Refl impossible

Uninhabited (Synth.End = (Synth.Rec x)) where
  uninhabited Refl impossible

Uninhabited (Synth.End = (Synth.Select a b c d e)) where
  uninhabited Refl impossible

Uninhabited (Synth.End = (Synth.Offer a b c d)) where
  uninhabited Refl impossible

Uninhabited (Synth.Call x = (Synth.Rec y)) where
  uninhabited Refl impossible

Uninhabited (Synth.Call x = (Synth.Select a b c d e)) where
  uninhabited Refl impossible

Uninhabited (Synth.Call x = (Synth.Offer a b c d)) where
  uninhabited Refl impossible

Uninhabited (Synth.Rec x = (Synth.Select a b c d e)) where
  uninhabited Refl impossible

Uninhabited (Synth.Rec x = (Synth.Offer a b c d)) where
  uninhabited Refl impossible


Uninhabited ((Synth.Select a b c d e) = (Synth.Offer x y z w)) where
  uninhabited Refl impossible


mutual
  namespace Branch
    export
    decEq : (a : Branch Local ks rs (f,s))
         -> (b : Branch Local ks rs (x,y))
              -> Dec (Equal a b)
    decEq (B f s contA) (B x y contB)
      = decDo $ do Refl <- decEq f x `otherwise` (\Refl => Refl)
                   Refl <- decEq s y `otherwise` (\Refl => Refl)
                   Refl <- Synth.decEq contA contB `otherwise` (\Refl => Refl)
                   pure Refl

  namespace Branches
    export
    decEq : (as : DList (String,Base)
                        (Branch Local ks rs)
                        (fs))
         -> (bs : DList (String,Base)
                        (Branch Local ks rs)
                        (gs))
              -> Dec (Equal as bs)
    decEq as bs with (shape as bs)
      decEq [] [] | Empty = Yes Refl
      decEq (x :: xs) [] | LH = No isLeftHeavy
      decEq [] (x :: xs) | RH = No isRightHeavy
      decEq (B xl xt cx :: xs) (B yl yt cy :: ys) | Same
        = decDo $ do Refl <- Branch.decEq (B xl xt cx) (B yl yt cy)
                               `otherwise` (\Refl => Refl)
                     Refl <- Branches.decEq xs ys `otherwise` (\Refl => Refl)
                     pure Refl

  public export
  decEq : (a,b : Local ks rs) -> Dec (Equal a b)
  decEq Crash Crash
    = Yes Refl
  decEq Crash End
    = No absurd
  decEq Crash (Call x)
    = No absurd
  decEq Crash (Rec x)
    = No absurd
  decEq Crash (Select kind whom ty prf choices)
    = No absurd

  decEq Crash (Offer kind whom ty prf)
    = No absurd


  decEq End Crash
    = No (negEqSym absurd)
  decEq End End
    = Yes Refl
  decEq End (Call x)
    = No absurd
  decEq End (Rec x)
    = No absurd
  decEq End (Select kind whom ty prf choices)
    = No absurd
  decEq End (Offer kind whom ty prf)
    = No absurd


  decEq (Call x) Crash
    = No (negEqSym absurd)

  decEq (Call x) End
    = No (negEqSym absurd)

  decEq (Call x) (Call y)
    = case Index.decEq x y of
           No no => No (\Refl => no (Same Refl Refl))
           Yes (Same Refl Refl) => Yes Refl

  decEq (Call x) (Rec y)
    = No absurd
  decEq (Call x) (Select kind whom ty prf choices)
    = No absurd
  decEq (Call x) (Offer kind whom ty prf)
    = No absurd

  decEq (Rec x) Crash
    = No (negEqSym absurd)
  decEq (Rec x) End
    = No (negEqSym absurd)
  decEq (Rec x) (Call y)
    = No (negEqSym absurd)

  decEq (Rec x) (Rec y) with (Synth.decEq x y)
    decEq (Rec x) (Rec x) | (Yes Refl)
      = Yes Refl
    decEq (Rec x) (Rec y) | (No contra)
      = No (\Refl => contra Refl)

  decEq (Rec x) (Select kind whom ty prf choices) = No absurd
  decEq (Rec x) (Offer  kind whom ty prf) = No absurd

  decEq (Select kind whom t p choices) Crash
    = No (negEqSym absurd)
  decEq (Select kind whom t p choices) End
    = No (negEqSym absurd)
  decEq (Select kind whom t p choices) (Call x)
    = No (negEqSym absurd)
  decEq (Select kind whom t p choices) (Rec x)
    = No (negEqSym absurd)

  decEq (Select roleX lX tX pX cX)
        (Select roleY lY tY pY cY)
    = case decEq roleX roleY Refl of
        No no => No (\Refl => no (Same Refl Refl))
        Yes (Same Refl Refl)
          => case decEq lX lY of
               No no => No (\Refl => no Refl)
               Yes Refl
                 => case decEq tX tY of
                      No no => No (\Refl => no Refl)
                      Yes Refl
                        => case decEq pX pY Refl of
                             Refl
                               => case Synth.decEq cX cY of
                                    No no => No (\Refl => no Refl)
                                    Yes Refl => Yes Refl

  decEq (Select kind whom t p choices) (Offer x type prfM y)
    = No absurd

  decEq (Offer kind whom t p) Crash
    = No (negEqSym absurd)
  decEq (Offer kind whom t p) End
    = No (negEqSym absurd)
  decEq (Offer kind whom t p) (Call x)
    = No (negEqSym absurd)
  decEq (Offer kind whom t p) (Rec x)
    = No (negEqSym absurd)
  decEq (Offer kind whom t p) (Select x label type prf cont)
    = No (negEqSym absurd)

  decEq (Offer roleX (Val (UNION (x:::xs))) (UNION (p::ps)) csX)
        (Offer roleY (Val (UNION (y:::ys))) (UNION (q::qs)) csY)
    = case decEq roleX roleY Refl of
        No no => No (\Refl => no (Same Refl Refl))
        Yes (Same Refl Refl)
          => case decEq (UNION (x:::xs)) (UNION (y:::ys)) of
               No no => No (\Refl => no Refl)
               Yes Refl
                 => case decEq (UNION (p::ps)) (UNION (q::qs)) Refl of
                      Refl
                        => case decEq csX csY of
                             No no => No (\Refl => no Refl)
                             Yes Refl => Yes Refl

  public export
  DecEq (Local ks rs) where
    decEq = Synth.decEq


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
