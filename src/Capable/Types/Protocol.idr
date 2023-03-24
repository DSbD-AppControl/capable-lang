|||
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
module Capable.Types.Protocol

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

%default total

public export
data Kind = R -- To capture recursion variables

export
DecEq Kind where
  decEq R R = Yes Refl

public export
data Branch : (0 contType : List Kind -> List Role -> Type)
           -> (  ks       : List Kind)
           -> (  rs       : List Role)
           -> (  f        : (String, Base))
                         -> Type
  where
    B : {0 contType : List Kind -> List Role -> Type}
     -> (l : String)
     -> (b : Base)
     -> (cont : contType ks rs)
             -> Branch contType ks rs (l,b)

namespace Branch
  public export
  data IsLabelled : (s : String)
                 -> (b : Branch c ks rs (s,t))
                      -> Type
    where
      HasLabel : IsLabelled s (B s b c)

public export
RecVar : List Kind -> Type
RecVar ks = IsVar ks R

namespace Global

  public export
  data Global : List Kind -> List Role -> Type where
    End : Global ks rs

    Call : {vs : _} -> RecVar vs -> Global vs rs

    Rec : Global (R::vs) rs
       -> Global     vs  rs

    Choice : {fs : _}
          -> (s : Role rs)
          -> (r : Role rs)
          -> (type   : Singleton (UNION (field:::fs)))
          -> (prfM   : Marshable (UNION (field:::fs)))
          -> (prfR   : Not (Equals Role (IsVar rs) s r))
          -> (opties : DList (String,Base)
                             (Branch Global ks rs)
                             (field::fs))
                    -> Global ks rs

  namespace Ty
    public export
    data Session : Type where
      S : {rs : _} -> Context Role rs -> Global Nil rs -> Session

namespace Local


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


  public export
  data Local : List Kind -> List Role -> Type where
    Crash : Local ks rs
    End : Local ks rs
    Call : {vs : _} -> RecVar vs -> Local vs rs
    Rec : Local (R::vs) rs -> Local vs rs
    Choice : {rs : _} -> (kind : ChoiceTy)
          -> (whom : Role rs)
          -> (type : Singleton (UNION (field:::fs)))
          -> (prfM   : Marshable (UNION (field:::fs)))
          -> (choices : DList (String,Base)
                              (Branch Local ks rs)
                              (field::fs))
                     -> Local ks rs

  Uninhabited (Local.Crash = Local.End) where
    uninhabited Refl impossible

  Uninhabited (Local.Crash = (Local.Call x)) where
    uninhabited Refl impossible

  Uninhabited (Local.Crash = (Local.Rec x)) where
    uninhabited Refl impossible

  Uninhabited (Local.Crash = (Local.Choice a b c d e)) where
    uninhabited Refl impossible

  Uninhabited (Local.End = (Local.Call x)) where
    uninhabited Refl impossible

  Uninhabited (Local.End = (Local.Rec x)) where
    uninhabited Refl impossible

  Uninhabited (Local.End = (Local.Choice a b c d e)) where
    uninhabited Refl impossible

  Uninhabited (Local.Call x = (Local.Rec y)) where
    uninhabited Refl impossible

  Uninhabited (Local.Call x = (Local.Choice a b c d e)) where
    uninhabited Refl impossible

  Uninhabited (Local.Rec x = (Local.Choice a b c d e)) where
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
                     Refl <- Local.decEq contA contB `otherwise` (\Refl => Refl)
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
    decEq Crash (Choice kind whom ty prf choices)
      = No absurd


    decEq End Crash
      = No (negEqSym absurd)
    decEq End End
      = Yes Refl
    decEq End (Call x)
      = No absurd
    decEq End (Rec x)
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

    decEq (Call x) (Rec y)
      = No absurd
    decEq (Call x) (Choice kind whom ty prf choices)
      = No absurd

    decEq (Rec x) Crash
      = No (negEqSym absurd)
    decEq (Rec x) End
      = No (negEqSym absurd)
    decEq (Rec x) (Call y)
      = No (negEqSym absurd)

    decEq (Rec x) (Rec y) with (Local.decEq x y)
      decEq (Rec x) (Rec x) | (Yes Refl)
        = Yes Refl
      decEq (Rec x) (Rec y) | (No contra)
        = No (\Refl => contra Refl)

    decEq (Rec x) (Choice kind whom ty prf choices) = No absurd

    decEq (Choice kind whom t p choices) Crash
      = No (negEqSym absurd)
    decEq (Choice kind whom t p choices) End
      = No (negEqSym absurd)
    decEq (Choice kind whom t p choices) (Call x)
      = No (negEqSym absurd)
    decEq (Choice kind whom t p choices) (Rec x)
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
                              Refl => decDo $ do Refl <- Branches.decEq cs zs `otherwise` (\Refl => Refl)
                                                 pure Refl

    public export
    DecEq (Local ks rs) where
      decEq = Local.decEq


    export
    branchesEq : (b  : Branch Local ks rs (l,t))
              -> (bs : DList (String, Base)
                             (Branch Local ks rs)
                             ls)
                    -> DecInfo ()
                               (All (String,Base)
                                    (Branch Local ks rs)
                                    (Equal b)
                                    ls
                                    bs)
    branchesEq b []
      = Yes []
    branchesEq b ((B str x cont) :: rest) with (Branch.decEq b (B str x cont))
      branchesEq b ((B str x cont) :: rest) | (Yes prf) with (branchesEq b rest)
        branchesEq b ((B str x cont) :: rest) | (Yes prf) | (Yes prfWhy)
          = Yes (prf :: prfWhy)
        branchesEq b ((B str x cont) :: rest) | (Yes prf) | (No _ no)
          = No () (\(h::t) => no t)

      branchesEq b ((B str x cont) :: rest) | (No no)
        = No () (\(h::t) => no h)

namespace Global
  public export
  Branches : List Kind -> List Role -> List (String, Base) -> Type
  Branches ks rs
    = DList (String, Base)
            (Branch Global ks rs)

namespace Local

  public export
  Branches : List Kind -> List Role -> List (String, Base)-> Type
  Branches ks rs
    = DList (String, Base)
            (Branch Local ks rs)



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
