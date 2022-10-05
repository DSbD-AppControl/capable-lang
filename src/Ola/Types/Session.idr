|||
|||
||| Module    : Ola.Types.Role
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
module Ola.Types.Session

import Decidable.Equality

import Toolkit.Decidable.Do

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
  namespace Ty

    public export
    data Global : List Kind -> List Role -> Type where
      End : Global ks rs

      Call : IsVar vs R -> Global vs rs

      Rec : Global (R::vs) rs
         -> Global     vs  rs

      Choice : (s : IsVar rs MkRole)
            -> (r : IsVar rs MkRole)
            -> (prf : Not (s = r))
            -> (opties : List1 (String, Base, Global ks rs))
                   -> Global vs rs

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

    public export
    data Local : List Kind -> List Role -> Type where
      End : Local ks rs
      Call : IsVar vs R -> Local ks rs
      Rec : Local (R::vs) rs -> Local vs rs
      Choice : (kind : ChoiceTy)
            -> (whom : IsVar rs MkRole)
            -> (choices : List1 (String, Base, Local ks rs))
                       -> Local ks rs


    public export
    decEq : (a,b : Local ks rs) -> Dec (Equal a b)

    public export
    DecEq (Local ks rs) where
      decEq = Local.Ty.decEq

namespace Projection

  public export
  data Project : (role : IsVar rs MkRole)
              -> (g    : Global ks rs)
              -> (l    : Local  ks rs)
                      -> Type
  namespace List
    public export
    data Project : (role : IsVar rs MkRole)
                -> (gs   : List (String, Base, Global ks rs))
                -> (ls   : List (String, Base, Local  ks rs))
                        -> Type

  namespace List1
    public export
    data Project : (role : IsVar rs MkRole)
                -> (gs   : List1 (String, Base, Global ks rs))
                -> (ls   : List1 (String, Base, Local  ks rs))
                        -> Type

  ||| Plain projection
  public export
  data Project : (role : IsVar rs MkRole)
              -> (g    : Global ks rs)
              -> (l    : Local  ks rs)
                      -> Type
    where
      End : Project whom End End
      Call : Project whome (Call idx) (Call idx)

      Rec : (rec : Project whom x y)
                -> Project whom (Rec x) (Rec y)

      Select : (prf : whom = s)
            -> (bs  : List1.Project whom                          xs ys)
                         -> Project whom (Choice        s r notsr xs)
                                         (Choice SELECT   r          ys)

      Offer : (prf : whom = r)
           -> (bs  : List1.Project whom                           xs ys)
                        -> Project whom (Choice        s r notstr xs)
                                        (Choice BRANCH s             ys)

      Merge : (prfS  : Not (whom = s))
           -> (prfR  : Not (whom = r))
           -> (bs    : List1.Project whom xs ((l,t,y):::ys))
           -> (merge : All (Equal (l,t,y)) ys)
                          -> Project whom (Choice s r notsr xs)
                                          y


  namespace List
    public export
    data Project : (role : IsVar rs MkRole)
                -> (gs   : List (String, Base, Global ks rs))
                -> (ls   : List (String, Base, Local  ks rs))
                        -> Type
      where
        Nil : Project whom Nil Nil
        (::) : Project whom         x               y
            -> Project whom             xs              ys
            -> Project whom ((xl,xt,x)::xs) ((yl,yt,y)::ys)

  namespace List1
    public export
    data Project : (role : IsVar rs MkRole)
                -> (gs   : List1 (String, Base, Global ks rs))
                -> (ls   : List1 (String, Base, Local  ks rs))
                        -> Type
      where
        Proj : Project whom (x::xs) (y::ys)
            -> Project whom (x:::xs) (y:::ys)

-- [ EOF ]
