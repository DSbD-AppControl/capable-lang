module Capable.Types.Protocol.Local

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
data ChoiceTy = BRANCH | SELECT

notBS : BRANCH = SELECT -> Void
notBS Refl impossible

export
DecEq ChoiceTy where
  decEq BRANCH BRANCH = Yes Refl
  decEq BRANCH SELECT = No notBS
  decEq SELECT BRANCH = No (negEqSym notBS)
  decEq SELECT SELECT = Yes Refl

||| The result of projection.

public export
data Local : List Kind -> List Role -> Type where
  Crash : Local ks rs -- @TODO no longer needed
  End : Local ks rs
  Call : {v, vs : _} -> RecVar vs v -> Local vs rs
  Rec : (v : Kind) -> Local (v::vs) rs -> Local vs rs
  Choice : {w,rs : _}
        -> (kind : ChoiceTy)
        -> (whom : Role rs w)
        -> (type : Singleton (UNION (field:::fs)))
        -> (prfM   : Marshable (UNION (field:::fs)))
        -> (choices : DList (String,Base)
                            (Branch Local ks rs)
                            (field::fs))
                   -> Local ks rs

public export
Branches : List Kind -> List Role -> List (String, Base)-> Type
Branches ks rs
  = DList (String, Base)
          (Branch Local ks rs)

Uninhabited (Local.Crash = Local.End) where
  uninhabited Refl impossible

Uninhabited (Local.Crash = (Local.Call x)) where
  uninhabited Refl impossible

Uninhabited (Local.Crash = (Local.Rec v x)) where
  uninhabited Refl impossible

Uninhabited (Local.Crash = (Local.Choice a b c d e)) where
  uninhabited Refl impossible

Uninhabited (Local.End = (Local.Call x)) where
  uninhabited Refl impossible

Uninhabited (Local.End = (Local.Rec v x)) where
  uninhabited Refl impossible

Uninhabited (Local.End = (Local.Choice a b c d e)) where
  uninhabited Refl impossible

Uninhabited (Local.Call x = (Local.Rec v y)) where
  uninhabited Refl impossible

Uninhabited (Local.Call x = (Local.Choice a b c d e)) where
  uninhabited Refl impossible

Uninhabited (Local.Rec v x = (Local.Choice a b c d e)) where
  uninhabited Refl impossible




public export
decEq : (a,b : Local ks rs) -> Dec (Equal a b)
decEq Crash Crash
  = Yes Refl
decEq Crash End
  = No absurd
decEq Crash (Call x)
  = No absurd
decEq Crash (Rec _ x)
  = No absurd
decEq Crash (Choice kind whom ty prf choices)
  = No absurd


decEq End Crash
  = No (negEqSym absurd)
decEq End End
  = Yes Refl
decEq End (Call x)
  = No absurd
decEq End (Rec _ x)
  = No absurd
decEq End (Choice kind whom ty prf choices)
  = No absurd

decEq (Call x) Crash
  = No (negEqSym absurd)

decEq (Call x) End
  = No (negEqSym absurd)

decEq (Call x) (Call y)
  = case Index.decEq x y of
         No no => No (\Refl => no (Same Refl Refl))
         Yes (Same Refl Refl) => Yes Refl

decEq (Call x) (Rec _ y)
  = No absurd
decEq (Call x) (Choice kind whom ty prf choices)
  = No absurd

decEq (Rec _ x) Crash
  = No (negEqSym absurd)
decEq (Rec _ x) End
  = No (negEqSym absurd)
decEq (Rec _ x) (Call y)
  = No (negEqSym absurd)

decEq (Rec a x) (Rec b y)
  = decDo $ do Refl <- decEq a b `otherwise` (\Refl => Refl)
               Refl <- Local.decEq x y `otherwise` (\Refl => Refl)
               pure Refl

decEq (Rec _ x) (Choice kind whom ty prf choices) = No absurd

decEq (Choice kind whom t p choices) Crash
  = No (negEqSym absurd)
decEq (Choice kind whom t p choices) End
  = No (negEqSym absurd)
decEq (Choice kind whom t p choices) (Call x)
  = No (negEqSym absurd)
decEq (Choice kind whom t p choices) (Rec _ x)
  = No (negEqSym absurd)
decEq (Choice a b (Val (UNION (f:::fs))) (UNION (h::hs)) cs)
      (Choice x y (Val (UNION (g:::gs))) (UNION (i::is)) zs)
  = case decEq a x of
      (No contra) => No (\case Refl => contra Refl)
      (Yes Refl)
        => case Index.decEq b y of
            (No contra) => No (\case Refl => contra (Same Refl Refl))
            (Yes (Same Refl Refl))
              => case decEq (UNION (f:::fs)) (UNION (g:::gs)) of
                   (No contra) => No (\case Refl => contra Refl)
                   (Yes Refl)
                     => case decEq (UNION (h::hs)) (UNION (i::is)) Refl of
                          Refl => decDo $ do Refl <- assert_total
                                                      $ Branches.decEq Local.decEq cs zs `otherwise` (\Refl => Refl)
                                             pure Refl

public export
DecEq (Local ks rs) where
  decEq = Local.decEq

public export
data BranchEQ : (a : Branch Local ks rs nt)
             -> (b : Branch Local ks rs mt)
                  -> Type where
  BEQ : x === y
     -> a === b
     -> BranchEQ (B l x a)
                 (B m y b)


export
branchEQ : (a : Branch Local ks rs nt)
        -> (b : Branch Local ks rs mt)
             -> Dec (BranchEQ a b)
branchEQ (B l x a) (B m y b)
  = case decEq x y of
      No no => No (\(BEQ g h) => no g)
      Yes Refl
        => case Local.decEq a b of
             No no => No (\(BEQ g h) => no h)
             Yes Refl => Yes (BEQ Refl Refl)

export
branchesEQ : (b  : Branch Local ks rs (l,t))
          -> (bs : DList (String, Base)
                         (Branch Local ks rs)
                         ls)
                -> DecInfo ()
                           (All (String,Base)
                                (Branch Local ks rs)
                                (BranchEQ b)
                                ls
                                bs)
branchesEQ b []
  = Yes []
branchesEQ b (x :: xs) with (branchEQ b x)
  branchesEQ b (x :: xs) | (Yes prf) with (branchesEQ b xs)
    branchesEQ b (x :: xs) | (Yes prf) | (Yes prfWhy)
      = Yes (prf :: prfWhy)
    branchesEQ b (x :: xs) | (Yes prf) | (No msg no)
      = No ()
           (\(h::t) => no t)

  branchesEQ b (x :: xs) | (No no)
    = No () (\(h::t) => no h)

namespace Closed
  export
  pretty : (kctxt : Context Kind ks)
        -> (rctxt : Context Ty.Role rs)
        -> (ltype : Local ks rs)
                 -> Doc ()
  pretty _ _ Crash
    = pretty "Crash"

  pretty _ _ End
    = pretty "End"

  pretty kctxt rctxt (Call x)
    = group
    $ hsep
      [ pretty "Call"
      , parens
        $ pretty
          $ reflect kctxt x
      ]

  pretty kctxt rctxt (Rec (R v) x)
    = let cont = pretty (extend kctxt v (R v)) rctxt x
      in group
      $  align
      $  vsep [ group (pretty "rec" <+> parens (pretty v) <+> pretty ".")
              , indent 2 cont]

  pretty kctxt rctxt (Choice BRANCH whom (Val (UNION (f:::fs))) _ cs)
    = group
    $ parens
    $ hsep
    [ hcat
      [ pretty "recvFrom"
      , brackets
        $ pretty
          $ reflect rctxt whom
      ]
--    , pretty (show (UNION (f:::fs)))
    , (assert_total $ branches pretty kctxt rctxt cs) ]


  pretty kctxt rctxt (Choice SELECT whom (Val (UNION (f:::fs))) _ cs)
    = group
    $ parens
    $ hsep
    [ hcat
      [ pretty "sendTo"
      , brackets
        $ pretty
          $ reflect rctxt whom
       ]
--    , pretty (show (UNION (f:::fs)))
    , (assert_total branches pretty kctxt rctxt cs)
    ]

  export
  toString : (rctxt : Context Ty.Role rs)
          -> (ltype : Local Nil rs)
                   -> String
  toString r l = show (pretty Nil r l)


  namespace Open

    export
    toString : (kctxt : Context Kind ks)
            -> (rctxt : Context Ty.Role rs)
            -> (ltype : Local ks rs)
                     -> String
    toString ks r l = show (pretty ks r l)

-- [ EOF ]
