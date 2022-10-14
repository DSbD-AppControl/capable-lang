|||
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
module Ola.Types.Protocol

import Decidable.Equality

import Toolkit.Decidable.Do
import public Toolkit.Decidable.Informative
import public Toolkit.Decidable.Equality.Indexed

import public Toolkit.DeBruijn.Renaming

import Data.List.Elem
import Data.List1
import Data.List.Quantifiers
import Ola.Types.Role
import Ola.Types.Base

%default total

public export
data Kind = R -- To capture recursion variables

namespace Global
  mutual
    namespace Ty
        public export
        data Global : List Kind -> List Role -> Type where
          End : Global ks rs

          Call : IsVar vs R -> Global vs rs

          Rec : Global (R::vs) rs
             -> Global     vs  rs

          Choice : (s : IsVar rs MkRole)
                -> (r : IsVar rs MkRole)
                -> (prf : Not (Equals Role (IsVar rs) s r))
                -> (opties : List1 (Global.Branch ks rs))
                       -> Global vs rs
    public export
    data Branch : List Kind -> List Role -> Type where
      B : String -> Base -> Global ks rs -> Branch ks rs

namespace Local
  namespace Ty

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

    mutual
      public export
      data Local : List Kind -> List Role -> Type where
        End : Local ks rs
        Call : IsVar vs R -> Local ks rs
        Rec : Local (R::vs) rs -> Local vs rs
        Choice : (kind : ChoiceTy)
              -> (whom : IsVar rs MkRole)
              -> (choices : List1 (Local.Branch ks rs))
                         -> Local ks rs

      namespace Local
        public export
        data Branch : List Kind -> List Role -> Type where
          B : String -> Base -> Local ks rs -> Branch ks rs

        public export
        data Extract : (Local.Branch ks rs) -> Local ks rs-> Type where
          E : Extract (B s b l) l

    public export
    decEq : (a,b : Local ks rs) -> Dec (Equal a b)

    public export
    DecEq (Local ks rs) where
      decEq = Local.Ty.decEq

    export
    branchEq : (a,b : Local.Branch ks rs) -> DecInfo () (a = b)
    branchEq a b = ?branchEq_rhs

    export
    branchesEq : (b  : Local.Branch ks rs)
              -> (bs : List (Local.Branch ks rs))
              -> DecInfo () (All (Equal b) bs)
{-
namespace Selection
  namespace List
    public export
    data Select : (label : String) -> List (String, Base, Local ks rs) -> (Base, Local ks rs) -> Type where
      Here : (prf : this = that)
                 -> Select this ((that,type,cont)::bs) (type,cont)

      There:  (later : Select this bs (type,cont))
                    -> Select this ((that,type',cont')::bs) (type,cont)
  namespace List1
    public export
    data Select : (label : String) -> List1 (String, Base, Local ks rs) -> (Base, Local ks rs) -> Type where
      S1 : Select this (b::bs)  (type,cont)
        -> Select this (b:::bs) (type,cont)


  public export
  data Select : (label : String) -> Local ks rs -> (Base, Local ks rs) -> Type where
    S : Select label                     bs  (type,cont)
     -> Select label (Choice SELECT whom bs) (type,cont)
-}
namespace Global
  public export
  Branches : List Kind -> List Role -> Type
  Branches ks rs
    = List (Global.Branch ks rs)


  public export
  Branches1 : List Kind -> List Role -> Type
  Branches1 ks rs
    = List1 (Global.Branch ks rs)

namespace Local

  public export
  Branches : List Kind -> List Role -> Type
  Branches ks rs
    = List (Local.Branch ks rs)


  public export
  Branches1 : List Kind -> List Role -> Type
  Branches1 ks rs
    = List1 (Local.Branch ks rs)

namespace Projection
  mutual
    namespace Branch

      public export
      data Project : (ks : List Kind)
                  -> (rs : List Role)
                  -> (role   : IsVar rs MkRole)
                  -> (global : Global.Branch ks rs)
                  -> (local  : Local.Branch  ks rs)
                            -> Type
        where
          B : (m : String)
           -> (t : Base)
           -> Protocol.Project ks rs role        g         l
           -> Branch.Project   ks rs role (B m t g) (B m t l)


      export
      funProject : Branch.Project ks rs whom b x ->
                   Branch.Project ks rs whom b y ->
                   x === y
      funProject (B m t p) (B m t q) = cong (B m t) (funProject p q)

    namespace Protocol
      ||| Plain projection
      public export
      data Project : (ks : List Kind)
                  -> (rs : List Role)
                  -> (role : IsVar rs MkRole)
                  -> (g    : Global ks rs)
                  -> (l    : Local  ks rs)
                          -> Type
        where
          End  : Project ks rs whom End End
          Call : Project ks rs whom (Call idx) (Call idx)

          Rec : (rec : Project (R::ks) rs whom      x       y)
                    -> Project ks rs whom (Rec x) (Rec y)

          Select : (prf : Equals Role (IsVar rs) whom s)
                -> (bs  : List1.Project ks rs whom                          xs ys)
                             -> Project ks rs whom (Choice        s r notsr xs)
                                                   (Choice SELECT   r          ys)

          Offer : (prf : Equals Role (IsVar rs) whom r)
               -> (bs  : List1.Project ks rs whom                           xs ys)
                            -> Project ks rs whom (Choice        s r notstr xs)
                                                  (Choice BRANCH s             ys)

          Merge : (prfS  : Not (Equals Role (IsVar rs) whom s))
               -> (prfR  : Not (Equals Role (IsVar rs) whom r))
               -> (prf   : Same1 ks rs whom gs (B l t c))
                        -> Project ks rs whom (Choice s r notsr gs)
                                         c

      export
      funProject : Protocol.Project ks rs whom b x ->
                   Protocol.Project ks rs whom b y ->
                   x === y
      funProject End End = Refl
      funProject Call Call = Refl
      funProject (Rec rec) (Rec z) = cong Rec (funProject rec z)
      funProject (Select {ys = ys1} (Same Refl Refl) ps) (Select {ys = ys2} (Same Refl Refl) qs)
        = cong (Choice SELECT _) (funProject ps qs)
      funProject (Select {notsr} (Same Refl Refl) bs) (Offer (Same Refl Refl) w)
        = void (notsr (Same Refl Refl))
      funProject (Select (Same Refl Refl) bs) (Merge prfS prfR z)
        = void (prfS (Same Refl Refl))
      funProject (Offer (Same Refl Refl) bs) (Select {notsr} (Same Refl Refl) w)
        = void (notsr (Same Refl Refl))
      funProject (Offer _ p) (Offer _ q) = cong (Choice BRANCH _) (funProject p q)
      funProject (Offer (Same Refl Refl) bs) (Merge prfS prfR z)
        = void (prfR (Same Refl Refl))
      funProject (Merge prfS prfR prf) (Select (Same Refl Refl) bs) = void (prfS (Same Refl Refl))
      funProject (Merge prfS prfR prf) (Offer (Same Refl Refl) bs) = void (prfR (Same Refl Refl))
      funProject (Merge _ _ p) (Merge _ _ q) = funSame1 p q

    namespace List
      public export
      data Project : (ks : List Kind)
                  -> (rs : List Role)
                  -> (role : IsVar rs MkRole)
                  -> (gs   : Global.Branches ks rs)
                  -> (ls   : Local.Branches  ks rs)
                          -> Type
        where
          Nil : Project ks rs whom Nil Nil
          (::) : Branch.Project ks rs whom  x       y
              -> List.Project   ks rs whom     xs      ys
              -> List.Project   ks rs whom (x::xs) (y::ys)

      export
      funProject : List.Project ks rs whom b x ->
                   List.Project ks rs whom b y ->
                   x === y
      funProject [] [] = Refl
      funProject (p :: ps) (q :: qs) = cong2 (::) (funProject p q) (funProject ps qs)

      namespace Same
        public export
        data Project : (ks : List Kind)
                    -> (rs : List Role)
                    -> (role : IsVar rs MkRole)
                    -> (gs   : Global.Branches ks rs)
                    -> (l    :  Local.Branch   ks rs)
                            ->  Type
          where
            First : Project ks rs whom g   l
                 -> Project ks rs whom [g] l

            Next : Project ks rs whom  j           l
                -> Project ks rs whom     (k::gs)  a
                -> (prf : l = a)
                -> Project ks rs whom (j::k::gs)   l

        export
        Uninhabited (Same.Project ks rs role Nil l) where
          uninhabited (First x) impossible
          uninhabited (Next x y) impossible

    namespace List1
      public export
      data Project : (ks : List Kind)
                  -> (rs : List Role)
                  -> (role : IsVar rs MkRole)
                  -> (gs   : Global.Branches1 ks rs)
                  -> (ls   : Local.Branches1  ks rs)
                          -> Type
        where
          Proj : Project ks rs whom (x:: xs) (y:: ys)
              -> Project ks rs whom (x:::xs) (y:::ys)

      export
      funProject : List1.Project ks rs whom b x ->
                   List1.Project ks rs whom b y ->
                   x === y
      funProject (Proj (p :: ps)) (Proj (q :: qs))
         = cong2 (:::) (funProject p q) (funProject ps qs)


      public export
      data Same1 : (ks : List Kind)
                -> (rs : List Role)
                -> (role : IsVar rs MkRole)
                -> (gs   : Global.Branches1 ks rs)
                -> (l    :  Local.Branch    ks rs)
                        -> Type
        where
          S1 : {l : _} -> {ls : _} -> (projs : List1.Project ks rs whom (g:::gs) (l:::ls))
             -> (prf   : All (Equal l) ls)
                     -> Same1             ks rs whom (g:::gs) l


      export
      funSame1 : Same1 ks rs whom gs (B l1 t1 x) ->
                 Same1 ks rs whom gs (B l2 t2 y) ->
                 x === y
      funSame1 (S1 (Proj (p :: ps)) eqp) (S1 (Proj (q :: qs)) eqq)
        = case funProject p q of Refl => Refl


-- [ EOF ]
