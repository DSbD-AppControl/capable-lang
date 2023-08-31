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
Local : List Kind -> List Role -> Type
Local = Protocol LOCAL

||| The result of projection.
{-
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
-}


public export
Branches : List Kind -> List Role -> List (String, Base)-> Type
Branches ks rs
  = DList (String, Base)
          (Branch Local ks rs)

public export
data Diag : (l,r : Local ks rs) -> Type
  where
    Crash : Diag Crash Crash
    End : Diag End End
    Call : (prfA, prfB : _) -> Diag (Call prfA) (Call prfB)
    Rec : (a,b : Kind)
       -> (kA : Local (a::ks) rs)
       -> (kB : Local (b::ks) rs)
             -> Diag (Rec a kA) (Rec b kB)
    Choice : (kA,kB : ChoiceTy)
          -> (wA    : Role rs ra)
          -> (wB    : Role rs rb)
          -> (typeA, typeB : _)
          -> (prfA, prfB : _)
          -> (cas : _)
          -> (cbs : _)
          -> Diag (ChoiceL kA wA typeA prfA cas)
                  (ChoiceL kB wB typeB prfB cbs)

export
diag : (l,r : Local ks rs) -> Maybe (Diag l r)
diag End End
  = Just End

diag (Call x) (Call y)
  = Just (Call x y)

diag (Rec a ka) (Rec b kb)
  = Just (Rec a b ka kb)

diag (ChoiceL ka wA tA pA ca)
     (ChoiceL kb wB tB pB cb)
       = Just (Choice ka kb
                      wA wB
                      tA tB
                      pA pB
                      ca cb)

diag Crash Crash
  = Just Crash
diag _ _ = Nothing

diagNot : (s : Local ks rs)
            -> Not (diag s s === Nothing)
diagNot End                                   = absurd
diagNot (Call x)                              = absurd
diagNot (Rec v x)                             = absurd
diagNot (ChoiceL kind whom type prfM choices) = absurd
diagNot Crash                                 = absurd


public export
DecEq (Local ks rs) where
  decEq a@_ b@_ with (diag a b) proof eq

    _ | (Just Crash)
          = Yes Refl

    _ | (Just End)
          = Yes Refl

    _ | (Just (Call prfA prfB))

          = case Index.decEq prfA prfB of
              No no => No (\Refl => no (Same Refl Refl))
              Yes (Same Refl Refl) => Yes Refl

    _ | (Just (Rec x y kA kB))

          = decDo $ do Refl <- decEq x y `otherwise` (\Refl => Refl)
                       Refl <- decEq kA kB `otherwise` (\Refl => Refl)
                       pure Refl
    _ | (Just (Choice kA kB
                      wA wB
                      (Val (UNION (f:::fs))) (Val (UNION (g:::gs)))
                      prfA prfB
                      cas cbs))
          = case decEq kA kB of
              (No contra) => No (\case Refl => contra Refl)
              (Yes Refl)
                => case Index.decEq wA wB of
                    (No contra) => No (\case Refl => contra (Same Refl Refl))
                    (Yes (Same Refl Refl))
                      => case decEq (UNION (f:::fs)) (UNION (g:::gs)) of
                           (No contra) => No (\case Refl => contra Refl)
                           (Yes Refl)
                             => case decEq prfA prfB Refl of
                                  Refl => case assert_total $ Branches.decEq decEq cas cbs of
                                            No contra => No (\case Refl => contra Refl)
                                            Yes Refl => Yes Refl

    _ | Nothing = No (\Refl => diagNot _ eq)

public export
data BranchEQ : (a : Branch (Protocol LOCAL) ks rs nt)
             -> (b : Branch (Protocol LOCAL) ks rs mt)
                  -> Type where
  BEQ : x === y
     -> a === b
     -> BranchEQ (B l x a)
                 (B m y b)


export
branchEQ : (a : Branch (Protocol LOCAL) ks rs nt)
        -> (b : Branch (Protocol LOCAL) ks rs mt)
             -> Dec (BranchEQ a b)
branchEQ (B l x a) (B m y b)
  = case decEq x y of
      No no => No (\(BEQ g h) => no g)
      Yes Refl
        => case decEq a b of
             No no => No (\(BEQ g h) => no h)
             Yes Refl => Yes (BEQ Refl Refl)

export
branchesEQ : (b  : Branch (Protocol LOCAL) ks rs (l,t))
          -> (bs : DList (String, Base)
                         (Branch (Protocol LOCAL) ks rs)
                         ls)
                -> DecInfo ()
                           (All (String,Base)
                                (Branch (Protocol LOCAL) ks rs)
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


namespace Shape
  public export
  data Shape : (l,r : Local ks rs) -> Type
    where
      Crash : Shape Crash Crash
      End : Shape End End
      Call : Shape (Call prfA) (Call prfB)
      Rec : Shape (Rec a kA) (Rec b kB)
      Offer : Shape (ChoiceL BRANCH wB typeB prfB cbs) (ChoiceL BRANCH wA typeA prfA cas)
      Select : Shape (ChoiceL SELECT wB typeB prfB cbs) (ChoiceL SELECT wA typeA prfA cas)


  export
  shape : (l,r : Local ks rs) -> Maybe (Shape l r)
  shape End End = Just End
  shape (Call x) (Call y) = Just Call
  shape (Rec v x) (Rec w y) = Just Rec
  shape (ChoiceL BRANCH _ _ _ _) (ChoiceL BRANCH _ _ _ _) = Just Offer
  shape (ChoiceL SELECT _ _ _ _) (ChoiceL SELECT _ _ _ _) = Just Select

  shape Crash Crash = Just Crash
  shape _ _ = Nothing

  urgh : shape x y = Nothing -> Shape x y -> Void
  urgh Refl Crash impossible
  urgh Refl End    impossible
  urgh Refl Call   impossible
  urgh Refl Rec    impossible
  urgh Refl Offer  impossible
  urgh Refl Select impossible


  public export
  data SameShapedHead : (x,y : Local ks rs) -> Type where
    SS : {x,y : Local ks rs} -> Shape x y -> SameShapedHead x y



  export
  sameShapedHead : (x,y : Local ks rs) -> Dec (SameShapedHead x y)
  sameShapedHead x y with (shape x y) proof evi
    sameShapedHead x y | Nothing
      = No (\case (SS prf) => urgh evi prf)
    sameShapedHead x y | (Just z)
      = Yes (SS z)

-- [ EOF ]
