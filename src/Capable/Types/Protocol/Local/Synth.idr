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
  Select : {w     : _}
        -> {rs,ks : _}
        -> (whom  : Role rs w)
        -> (label : String)
        -> (type  : Base)
        -> (prf   : Marshable type)
        -> (cont  : Local ks rs)
                 -> Local ks rs

  Offer : {o       : _}
       -> {rs,ks   : _}
       -> (whom    : Role rs o)
       -> (type    : Singleton (UNION (field:::fs)))
       -> (prfM    : Marshable (UNION (field:::fs)))
       -> (choices : DList (String,Base)
                           (Branch Local ks rs)
                           (field::fs))
                  -> Local ks rs

  Choices : {rs,ks:_} -> (left,right : Local ks rs)
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

Uninhabited (Synth.Crash = (Synth.Choices a b)) where
  uninhabited Refl impossible

Uninhabited (Synth.End = (Synth.Call x)) where
  uninhabited Refl impossible

Uninhabited (Synth.End = (Synth.Rec x)) where
  uninhabited Refl impossible

Uninhabited (Synth.End = (Synth.Select a b c d e)) where
  uninhabited Refl impossible

Uninhabited (Synth.End = (Synth.Offer a b c d)) where
  uninhabited Refl impossible

Uninhabited (Synth.End = (Synth.Choices a b)) where
  uninhabited Refl impossible

Uninhabited (Synth.Call x = (Synth.Rec y)) where
  uninhabited Refl impossible

Uninhabited (Synth.Call x = (Synth.Select a b c d e)) where
  uninhabited Refl impossible

Uninhabited (Synth.Call x = (Synth.Offer a b c d)) where
  uninhabited Refl impossible

Uninhabited (Synth.Call x = (Synth.Choices a b)) where
  uninhabited Refl impossible

Uninhabited (Synth.Rec x = (Synth.Select a b c d e)) where
  uninhabited Refl impossible

Uninhabited (Synth.Rec x = (Synth.Offer a b c d)) where
  uninhabited Refl impossible

Uninhabited (Synth.Rec x = (Synth.Choices a b)) where
  uninhabited Refl impossible

Uninhabited ((Synth.Select a b c d e) = (Synth.Offer x y z w)) where
  uninhabited Refl impossible

Uninhabited ((Synth.Select a b c d e) = (Synth.Choices x y)) where
  uninhabited Refl impossible

Uninhabited ((Synth.Offer a b c d) = (Synth.Choices x y)) where
  uninhabited Refl impossible

mutual

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

  decEq Crash (Choices l r)
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
  decEq End (Choices l r)
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
  decEq (Call x) (Choices l r)
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
  decEq (Rec x) (Choices l r)
    = No absurd


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
    = case Index.decEq roleX roleY of
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
  decEq (Select kind whom t p choices) (Choices l r)
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
    = case Index.decEq roleX roleY of
        No no => No (\Refl => no (Same Refl Refl))
        Yes (Same Refl Refl)
          => case decEq (UNION (x:::xs)) (UNION (y:::ys)) of
               No no => No (\Refl => no Refl)
               Yes Refl
                 => case decEq (UNION (p::ps)) (UNION (q::qs)) Refl of
                      Refl
                        => case assert_total $ decEq Synth.decEq csX csY of
                             No no => No (\Refl => no Refl)
                             Yes Refl => Yes Refl

  decEq (Offer kind whom t p) (Choices l r)
    = No absurd

  decEq (Choices l r) Crash
    = No (negEqSym absurd)
  decEq (Choices l r) End
    = No (negEqSym absurd)
  decEq (Choices l r) (Call x)
    = No (negEqSym absurd)
  decEq (Choices l r) (Rec x)
    = No (negEqSym absurd)
  decEq (Choices l r) (Select whom label type prf cont)
    = No (negEqSym absurd)
  decEq (Choices l r) (Offer whom type prfM choices)
    = No (negEqSym absurd)
  decEq (Choices l r) (Choices left right)
    = decDo $ do Refl <- Synth.decEq l left  `otherwise` (\Refl => Refl)
                 Refl <- Synth.decEq r right `otherwise` (\Refl => Refl)
                 pure Refl

  public export
  DecEq (Local ks rs) where
    decEq = Synth.decEq


namespace Closed

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
    , hang 2 (assert_total $ branches pretty acc kctxt rctxt cs) ]

  pretty acc kctxt rctxt (Choices l r)
    = group
    $ parens
    $ hsep
    [ pretty "Choices"
    , hang 2 $ pretty acc kctxt rctxt l
    , hang 2 $ pretty acc kctxt rctxt r]

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
