||| Session Types and common actions on them.
|||
|||
module Capable.Types.Protocol.Common

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
import public Toolkit.Data.DList.Any

import public Toolkit.DeBruijn.Renaming

import Capable.Bootstrap
import Capable.Types.Role
import Capable.Types.Base

%default total


namespace Protocol
  ||| Protocols are either global or local.
  public export
  data View = GLOBAL | LOCAL

  ||| Recursion variables are stringly defined, but also nameless.
  public export
  data Kind = R String -- To capture recursion variables

  export
  DecEq Kind where
    decEq (R a) (R b)
      = decDo $ do Refl <- decEq a b `otherwise` (\Refl => Refl)
                   pure Refl

  ||| A labelled choice.
  |||
  ||| Made higher-order to support better reasoning about branches.
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

  ||| Recursion variables are nameless.
  public export
  RecVar : List Kind -> Kind  -> Type
  RecVar = IsVar

  ||| A helper (for pretty printing) to get the set of labels in a
  ||| collection of branches.
  export
  getLTs : DList (String, Base)
                 (Branch t ks rs)
                 bs
         -> Singleton bs
  getLTs []
    = Val []
  getLTs ((B l b cont) :: rest) with (getLTs rest)
    getLTs ((B l b cont) :: rest) | (Val xs)
      = Val ((l, b) :: xs)

  ||| To support singular representation of local actions on branch
  ||| collections.
  namespace Choice
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

  ||| A unified datatype for representing 'Session Types'.
  |||
  ||| Protocols must be well-scoped over recusrion variables and
  ||| roles.
  public export
  data Protocol : (viewpoint  : View)
               -> (ctxt_rvars : List Kind)
               -> (ctxt_roles : List Role)
                             -> Type
    where
      ||| End of the protocol.
      End : Protocol a ks rs

      ||| Recursive call.
      Call : {v,vs : _} -> RecVar vs v -> Protocol a vs rs

      ||| Define a fixed point.
      Rec : (v : Kind)
         -> Protocol a (v::vs) rs
         -> Protocol a     vs  rs

      ||| Global choice.
      ChoiceG : {x,y, fs : _}
             -> (s : Role rs x)
             -> (r : Role rs y)
             -> (type   : Singleton (UNION (field:::fs)))
             -> (prfM   : Marshable (UNION (field:::fs)))
             -> (prfR   : Not (REquals rs s r))
             -> (opties : DList (String,Base)
                                (Branch (Protocol GLOBAL) ks rs)
                                (field::fs))
                       -> Protocol GLOBAL ks rs

      ||| Local choice.
      ChoiceL : {w,rs : _}
             -> {field, fs : _}
             -> (kind : ChoiceTy)
             -> (whom : Role rs w)
             -> (type : Singleton (UNION (field:::fs)))
             -> (prfM   : Marshable (UNION (field:::fs)))
             -> (choices : DList (String,Base)
                                 (Branch (Protocol LOCAL) ks rs)
                                 (field::fs))
                        -> Protocol LOCAL ks rs

      ||| Only local types can crash.
      Crash : Protocol LOCAL ks rs


||| Predicates on Branches.
namespace Branch
  ||| Does the branch have the given label.
  public export
  data IsLabelled : (s : String)
                 -> (b : Branch c ks rs (s,t))
                      -> Type
    where
      HasLabel : IsLabelled s (B s b c)

  ||| Are two branches equal.
  export
  decEq : (g : (i,j : c ks rs) -> Dec (Equal i j))
       -> (a : Branch c ks rs (f,s))
       -> (b : Branch c ks rs (x,y))
            -> Dec (Equal a b)
  decEq g (B f s contA) (B x y contB)
    = decDo $ do Refl <- decEq f x `otherwise` (\Refl => Refl)
                 Refl <- decEq s y `otherwise` (\Refl => Refl)
                 Refl <- g contA contB `otherwise` (\Refl => Refl)
                 pure Refl

  ||| Do the two branches share a label.
  public export
  data ShareLabel : (x : Branch (Protocol k) ks rs a)
                 -> (y : Branch (Protocol k) ks rs b)
                      -> Type
    where
      IsShared : ShareLabel (B l tx cx) (B l ty cy)

  ||| Do the two branches share a label.
  export
  isShared : (x : Branch (Protocol k) ks rs a)
          -> (y : Branch (Protocol k) ks rs b)
               -> DecInfo () (ShareLabel x y)
  isShared (B x tx cx) (B y ty cy) with (decEq x y)
    isShared (B x tx cx) (B x ty cy) | (Yes Refl)
      = Yes IsShared
    isShared (B x tx cx) (B y ty cy) | (No contra)
      = No () (\IsShared => contra Refl)

  public export
  SharedLabel : {lts : _}
            -> (ks : List Kind)
            -> (rs : List Role)
            -> (  x  : Branch (Protocol k) ks rs ltx)
            -> (  xs : DList (String, Base)
                             (Branch (Protocol k) ks rs)
                             lts)
                    -> Type
  SharedLabel ks rs x
    = DList.Any.Any (String, Base)
          (Branch (Protocol k) ks rs)
          (ShareLabel x)

  ||| Is there a common label between the given branch, and set of
  ||| branches?
  export
  sharedLabel : (  x  : Branch (Protocol k) ks rs ltx)
             -> (  xs : DList (String, Base)
                              (Branch (Protocol k) ks rs)
                              lts)
                     -> Dec (SharedLabel ks rs x xs)
  sharedLabel x xs with (DList.Any.any (isShared x) xs)
    sharedLabel x xs | (Yes prf)
      = Yes prf
    sharedLabel x xs | (No contra)
      = No contra


||| Actions on Branch Collections
namespace Branches

  ||| Are the two given collections equal.
  |||
  ||| It is higher order as we do not know what the continuation
  ||| type is!
  export
  decEq : (g : (i,j : c ks rs) -> Dec (Equal i j))
       -> (as : DList (String,Base)
                      (Branch c ks rs)
                      (fs))
       -> (bs : DList (String,Base)
                      (Branch c ks rs)
                      (gs))
            -> Dec (Equal as bs)
  decEq g as bs with (shape as bs)
    decEq g [] [] | Empty = Yes Refl
    decEq g (x :: xs) [] | LH = No isLeftHeavy
    decEq g [] (x :: xs) | RH = No isRightHeavy
    decEq g (B xl xt cx :: xs) (B yl yt cy :: ys) | Same
      = decDo $ do Refl <- decEq xl yl `otherwise` (\Refl => Refl)
                   Refl <- decEq xt yt `otherwise` (\Refl => Refl)
                   Refl <- g cx cy `otherwise` (\Refl => Refl)
                   Refl <- Branches.decEq g xs ys `otherwise` (\Refl => Refl)
                   pure Refl


||| Pretty printing of Protocols.
namespace Pretty

  export
  choices : List (Doc ann) -> Doc ann
  choices = group . encloseSep (flatAlt (pretty "{ ") (pretty "{"))
                               (flatAlt (pretty " }")  (pretty "}"))
                               (flatAlt (pretty "| ") (pretty " | "))

  branch : (pretty : Context Kind ks
                  -> Context Ty.Role rs
                  -> Protocol v ks rs
                  -> Doc ())
        -> (kctxt : Context Kind ks)
        -> (rctxt : Context Ty.Role rs)
        -> Branch (Protocol v) ks rs l
        -> Doc ()
  branch g kctxt rctxt (B label type c)
    = group
    $ align
    $ vcat
    [ pretty label <+> parens (pretty (show type))
    , pretty "." <+> g kctxt rctxt c
    ]


  branches : (pretty : Context Kind ks
                    -> Context Ty.Role rs
                    -> Protocol v ks rs
                    -> Doc ())
          -> (kctxt : Context Kind ks)
          -> (rctxt : Context Ty.Role rs)
          -> (bs    : DList (String,Base)
                            (Branch (Protocol v) ks rs)
                            ls)
                   -> Doc ()
  branches g kctxt rctxt xs
    = let prettyXS = mapToList (branch g kctxt rctxt) xs
      in assert_total
      $ choices prettyXS

  export
  pretty : (kctxt : Context Kind ks)
        -> (rctxt : Context Ty.Role rs)
        -> (type  : Protocol v ks rs)
                 -> Doc ()
  pretty kctxt rctxt End = pretty "End"

  pretty kctxt rctxt (Call x)
    = group
      $ hsep
        [ pretty "Call"
        , parens
          $ pretty
            $ reflect kctxt x
        ]

  pretty kctxt rctxt (Rec (R v) y)
      = let cont = pretty (extend kctxt v (R v)) rctxt y
      in group
      $  align
      $  vsep [ group
                $ pretty "rec" <+>
                  parens (pretty v) <+>
                  pretty "."
              , indent 2 cont]

  pretty kctxt rctxt (ChoiceG s r type prfM prfR opties)
    = group
      $ parens
        $ hsep
          [ pretty
            $ reflect rctxt s
          , pretty "==>"
          , pretty
            $ reflect rctxt r
          , (assert_total $ branches pretty kctxt rctxt opties)
          ]


  pretty kctxt rctxt (ChoiceL kind whom type prfM choices)
    = group
      $ parens
        $ hsep
        [ hcat
          [ case kind of
              BRANCH => pretty "recvFrom"
              SELECT => pretty "sendTo"
          , brackets
            $ pretty
              $ reflect rctxt whom
          ]
        , (assert_total $ branches pretty kctxt rctxt choices)
        ]


  pretty kctxt rctxt Crash
    = pretty "Crash"

  export
  toString : (kctxt : Context Kind ks)
          -> (rctxt : Context Ty.Role rs)
          -> (ltype : Protocol v ks rs)
                   -> String
  toString ks r l = show (pretty ks r l)

  namespace Closed
    export
    toString : (rctxt : Context Ty.Role rs)
            -> (ltype : Protocol v Nil rs)
                     -> String
    toString = toString Nil


-- [ EOF ]
