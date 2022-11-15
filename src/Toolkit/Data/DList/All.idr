module Toolkit.Data.DList.All

import Toolkit.Decidable.Informative

import Toolkit.Data.DList

import public Toolkit.Decidable.Equality.Indexed

%default total

||| Proof that all elements satisfies the predicate
|||
||| @idx   The type of the element's index.
||| @type  The type of the list element.
||| @p     A predicate
||| @xs      The list itself.
public export
data All : (kind : Type)
        -> (type : kind -> Type)
        -> (p      : {i : kind} -> (x : type i) -> Type)
        -> (is     : List kind)
        -> (xs     : DList kind type is)
                    -> Type

    where
      ||| Proof that the element is at the front of the list.
      Nil : {0 p : {i : kind} -> (x : type i) -> Type}
         -> All kind type p Nil Nil


      ||| Proof that the element is found later in the list.
      (::) : {0 p   : {i : kind} -> (x : type i) -> Type}
          -> (prf   : p x)
          -> (later : All kind type p ks xs)
                   -> All kind type p (k::ks) (x::xs)



export
all : {0 p : {i : kind} -> (x : type i) -> Type}
   -> (  f : {i : kind} -> (x : type i) -> Dec (p x))
   -> ( xs : DList kind type is)
          -> Dec (All kind type p is xs)
all f []
  = Yes []
all f (elem :: rest) with (f elem)
  all f (elem :: rest) | (Yes prf) with (all f rest)
    all f (elem :: rest) | (Yes prf) | (Yes prfs)
      = Yes (prf :: prfs)

    all f (elem :: rest) | (Yes prf) | (No no)
      = No (\case (x :: later) => no later)

  all f (elem :: rest) | (No no)
    = No (\case (x::later) => no x)

-- [ EOF ]
