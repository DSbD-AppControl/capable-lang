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


-- [ EOF ]
