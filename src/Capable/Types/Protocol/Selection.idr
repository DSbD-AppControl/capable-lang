|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Capable.Types.Protocol.Selection

import Decidable.Equality
import Data.String

import public Data.Singleton

import Data.List.Elem
import Data.List1
import Data.List.Quantifiers

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

import Capable.Types.Protocol

%default total

public export
data Select : (this : Branch Local ks rs (l,t))
           -> (prf  : Marshable (l,t))
           -> (from : DList (String,Base)
                            (Branch Local ks rs)
                            (field::fs))
           -> (prfM : DList (String,Base)
                            Marshable
                            (field::fs))
                   -> Type
  where
    Here :  Select b f (b::bs) (f::fs)
    There : Select b f      bs       fs
         -> Select b f (b'::bs) (f'::fs)

public export
data Result : (s : String)
           -> (from : DList (String,Base)
                            (Branch Local ks rs)
                            (fs))
           -> (prfM : DList (String,Base)
                            Marshable
                            (fs))
           -> Type
  where
    R : (t : Base) -> (c : Local ks rs)
     -> (prf : Marshable (s,t))
     -> Select (B s t c) prf from prfM -> Result s from prfM


export
select : (s : String)
      -> (prf : DList (String, Base) Marshable ((f::fs)))
      -> (bs  : DList (String, Base) (Branch Local ks rs) (f::fs))
             -> Dec (Result s bs prf )
select s (p::[]) ((B l b cont) :: []) with (decEq s l)
  select s (p::[]) ((B s b cont) :: []) | (Yes Refl)
    = Yes (R b cont p Here)
  select s (p::[]) ((B l b cont) :: []) | (No contra)
    = No (\case (R b cont (F s y) Here) => contra Refl)

select s (p::(p' :: ps)) ((B l b cont) :: (b'::bs)) with (decEq s l)
  select s (p::(p' :: ps)) ((B s b cont) :: (b'::bs)) | (Yes Refl)
    = Yes (R b cont p Here)
  select s (p::(p' :: ps)) ((B l b cont) :: (b'::bs)) | (No contra) with (select s (p'::ps) (b'::bs))
    select s (p::(p' :: ps)) ((B l b cont) :: (b'::bs)) | (No contra) | (Yes (R t c prf x))
      = Yes (R t c prf (There x))
    select s (p::(p' :: ps)) ((B l b cont) :: (b'::bs)) | (No contra) | (No g)
      = No (\case (R b cont (F l x) Here) => contra Refl
                  (R t c prf (There x)) => g (R t c prf x))


-- [ EOF ]
