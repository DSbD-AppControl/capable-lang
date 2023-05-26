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

import public Toolkit.DeBruijn.Renaming


import Capable.Bootstrap
import Capable.Types.Role
import Capable.Types.Base

%default total

namespace Protocol
  public export
  data Kind = R String -- To capture recursion variables

  export
  DecEq Kind where
    decEq (R a) (R b)
      = decDo $ do Refl <- decEq a b `otherwise` (\Refl => Refl)
                   pure Refl

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


  namespace Branch
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

  namespace Branches
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
  public export
  RecVar : List Kind -> Kind  -> Type
  RecVar = IsVar

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

export
choices : List (Doc ann) -> Doc ann
choices = group . encloseSep (flatAlt (pretty "[ ") (pretty "["))
                             (flatAlt (pretty "]")  (pretty "]"))
                             (flatAlt (pretty "| ") (pretty " | "))

branch : (Context Kind ks -> Context Ty.Role rs -> c ks rs -> Doc ())
      -> (kctxt : Context Kind ks)
      -> (rctxt : Context Ty.Role rs)
      -> Branch c ks rs l
      -> Doc ()
branch g kctxt rctxt (B label type c)
  = group
  $ align
  $ vcat
  [ pretty label <+> parens (pretty (show type))
  , pretty "." <+> g kctxt rctxt c
  ]

export
branches : (Context Kind ks -> Context Ty.Role rs -> c ks rs -> Doc ())
        -> (kctxt : Context Kind ks)
        -> (rctxt : Context Ty.Role rs)
        -> (bs    : DList (String,Base)
                          (Branch c ks rs)
                          ls)
                 -> Doc ()
branches g kctxt rctxt xs
  = let prettyXS = mapToList (branch g kctxt rctxt) xs
    in assert_total
    $ choices prettyXS

--export
--showAcc : Nat -> String
--showAcc n
--    = if lt n 26
--           then singleton (chr (cast (plus 97 n)))
--           else (singleton (chr (cast (plus 97 (mod n 26))))) <+> (assert_total $ showAcc  (minus n 26))
-- [ EOF ]
