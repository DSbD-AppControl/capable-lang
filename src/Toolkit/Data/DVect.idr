-- --------------------------------------------------------------- [ DVect.idr ]
-- Module    : DVect.idr
-- Copyright : (c) 2015,2016 See CONTRIBUTORS.md
-- License   : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]
||| A `list` construct to create lists of dependent types.
|||
||| One of the problems with using dependent types is that types
||| depend on values. This affects the ability to construct lists of
||| values that have a dependent type. The existing `List` type cannot
||| be used as it requires all elements to have the same type.
module Toolkit.Data.DVect

import Data.Nat
import Data.String

import public Data.Vect
import public Data.Vect.Elem

import public Toolkit.Decidable.Equality.Indexed

%default total


||| A list construct for dependent types.
|||
||| @aTy    The type of the value contained within the list element type.
||| @len    The length of the list.
||| @elemTy The type of the elements within the list
||| @as     The List used to contain the different values within the type.
public export
data DVect : (aTy : Type)
          -> (elemTy : aTy -> Type)
          -> (len : Nat)
          -> (as : Vect len aTy)
          -> Type where
  ||| Create an empty List
  Nil  : DVect aTy elemTy Z Nil
  ||| Cons
  |||
  ||| @ex The element to add
  ||| @rest The list for `elem` to be added to.
  (::) : {x : aTy}
      -> (ex : elemTy x)
      -> (rest : DVect aTy elemTy n xs)
      -> DVect aTy elemTy (S n) (x::xs)

public export
size : DVect a e l as -> Nat
size Nil = Z
size (x::xs) = 1 + size xs

public export
mapToVect : (forall x . e x -> b)
         -> DVect a e n xs
         -> Vect n b
mapToVect _ Nil = Nil
mapToVect f (x::xs) = f x :: mapToVect f xs


export
fromVect : {x : _} -> Vect n (e x)
        -> DVect a e n (replicate n x)
fromVect [] = []
fromVect (y :: xs)
  = y :: fromVect xs

export
fromList : {x : _} -> (xs : List (e x))
        -> DVect a e (length xs) (replicate (length xs) x)
fromList [] = []
fromList (y :: xs) = y :: fromList xs

export
toList : (xs : DVect a e n ts)
            -> List (DPair a e)
toList [] = []
toList (ex :: rest)
  = (_ ** ex) :: toList rest

||| Function to show a `DList`.
|||
||| Due to limitations in idris wrt to class instances on dependent
||| types a generic show instance cannot be defined for
||| sigmalist. This will cause minor annoyances in its use.
|||
||| @showFunc A function to show the elements
||| @l       The list to be Shown.
public export
showDVect : (showFunc : forall a . elemTy a -> String)
         -> (l : DVect aTy elemTy n as)
         -> String
showDVect f xs = "[" ++ unwords asList ++ "]"
  where
    toList : Vect q a -> List a
    toList Nil = Nil
    toList (x::xs) = x :: toList xs

    asList : List String
    asList = toList $ intersperse "," (mapToVect f xs)

namespace Alternative
  public export
  index : DVect aTy elemTy n as
       -> Elem a as
       -> elemTy a
  index (x::xs) Here = x
  index (x::xs) (There later) = index xs later

  public export
  update : (vs  : DVect iTy eTy l is)
        -> (idx : Elem i is)
        -> (new : eTy i)
        -> DVect iTy eTy l is
  update (ex :: rest) Here new = new :: rest
  update (ex :: rest) (There later) new = ex :: update rest later new

public export
update : {things : Vect n kind}
      -> (vs  : DVect kind type n things)
      -> (idx : Fin n)
      -> (new : type (index idx things))
             -> DVect kind type n things
update (ex :: rest) FZ new = new :: rest
update (ex :: rest) (FS x) new = ex :: update rest x new

public export
index : (vs  : DVect kind type n things)
     -> (idx : Fin n)
            -> type (index idx things)
index (ex :: rest) FZ
  = ex
index (ex :: rest) (FS x)
  = index rest x

-- --------------------------------------------------------------------- [ EOF ]
