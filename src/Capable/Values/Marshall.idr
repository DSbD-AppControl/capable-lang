||| Marshalling valus from/to the wire.
|||
||| Copyright : COPYRIGHT
||| License   : see LICENSE
|||
module Capable.Values.Marshall

import Decidable.Equality

import Data.List.Elem
import Data.List1.Elem
import Data.Vect
import Data.String

import System.Escape

import public Data.Singleton

import public System.File

import public Language.JSON
import Text.PrettyPrint.Prettyprinter

import Toolkit.Data.DList
import Toolkit.Data.DVect
import Toolkit.Data.List.AtIndex
import Toolkit.DeBruijn.Renaming

import Capable.Bootstrap
import Capable.Core
import Capable.Types
import Capable.Values


%default total

-- # Rug Adaptations

throw : Marshall.Error -> Capable a
throw = (throw . Marsh)

mismatch : (prf : Marshall.Marshable ty) -> (raw : JSON)
              -> Capable a
mismatch prf raw = throw (Mismatch prf raw)

mutual

  fieldsToJSON : (values : DList (String, Base) (Field store) tys)
              -> (prfs   : DList (String, Base) Marshable tys)
                        -> (List (String, JSON))
  fieldsToJSON [] []
    = Nil

  fieldsToJSON ((F l v) :: vs) ((F l p) :: ps)
    =    let x  = toJSON v p
      in let xs = fieldsToJSON vs ps

      in (l,x)::xs

  vectorToJSON : (value : Value store (VECTOR ty n) )
              -> (prf   : Marshable ty)
                       -> List JSON
  vectorToJSON (MkVect []) prf
    = Nil
  vectorToJSON (MkVect (x :: xs)) prf
    =  let x  = toJSON x prf
    in let xs = assert_total $ vectorToJSON (MkVect xs) prf
    in x::xs

  tupleToJSON : (c     : Nat )
             -> (value : DVect Base (Value store) n types)
             -> (prf   : DVect Base Marshable     n types)
                      -> List (String, JSON)
  tupleToJSON _ value []
    = Nil
  tupleToJSON c (v :: vs) (p :: ps)
    =    let x  = toJSON v p
      in let xs = tupleToJSON (S c) vs ps
      in (cast c, x)::xs

  toJSON : (val : Value store ty)
        -> (prf : Marshable ty)
               -> JSON
  toJSON (C c) CHAR
    = JString (cast c)

  toJSON (S str) STR
    = JString str

  toJSON (I i) INT
    = JNumber (cast i)

  toJSON (B x) BOOL
    = JBoolean x

  toJSON U UNIT
    = JNull

  toJSON (MkList xs) (LIST prf)
    = JArray
    $ assert_total
    $ map (\x => toJSON x prf) xs

  toJSON val (VECTOR ty n)
    =    let n  = (JNumber (cast n))
      in let xs = vectorToJSON val ty

      in JArray xs

  toJSON (Tuple y) (TUPLE x)
    = let xs = tupleToJSON 1 y x
      in JObject xs

  toJSON (Record x) (RECORD fields)
    = let xs = fieldsToJSON x fields
      in JObject xs

  toJSON (Tag s prf x) (UNION fields)
      =    let (F s p) = index fields prf
        in let x       = toJSON x p
        in JObject [(s,x)]

export
marshall : (prf : Marshable (l,ty))
        -> (val : Value store ty)
               -> Capable JSON
marshall (F l x) val
  = do let x = toJSON val x
       pure (JObject [(l,x)])


toChar : String -> Maybe Char
toChar str with (strM str)
  toChar "" | StrNil
    = Nothing
  toChar (strCons x xs) | (StrCons x xs) with (strM xs)
    toChar (strCons x "") | (StrCons x "") | StrNil
      = Just x
    toChar (strCons x (strCons c str)) | (StrCons x (strCons c str)) | (StrCons c str)
      = Nothing

toInt : Double -> Maybe Int
toInt d
  = if ((abs d) - (floor d)) == 0
    then Just (cast {to=Int} d)
    else Nothing


isElem : (s      : String)
      -> (xs     : DList (String, Base) Marshable types)
                -> Maybe (DPair Base (\x => Elem (s,x) types))
isElem s []
  = Nothing
isElem s (F s' x :: xs)
  = case decEq s s' of
      No _ => do (x' ** prf) <- isElem s xs
                 pure (x' ** There prf)
      Yes Refl => pure (_ ** Here)

mutual

  vectorFromJSON : {ty  : _}
                -> (prf : Marshable ty)
                -> (x   : Nat)
                -> (nat : Nat)
                -> (rs  : List JSON)
                       -> Capable (Value Nil (VECTOR ty nat))
  vectorFromJSON prf _ 0 []
    = pure (MkVect Nil)

  vectorFromJSON prf n (S k) []
    = throw (MissingElems (S k) (VECTOR prf n))

  vectorFromJSON prf n 0 (x :: xs)
    = throw (RedundantElems
                            (VECTOR prf n)
                            (JArray (x::xs)))

  vectorFromJSON prf n (S k) (x :: xs)
    = do x <- fromJSON prf x
         (MkVect xs) <- vectorFromJSON prf n k xs
         pure (MkVect (x::xs))


  tupleFromJSON : (prfs  : DVect Base Marshable n types)
               -> (c     : Nat)
               -> (rs    : List (String, JSON))
                        -> Capable (DVect Base (Value Nil) n types)
  tupleFromJSON [] _ []
    = pure Nil

  tupleFromJSON (p :: ps) _ []
    = throw (MissingUples (p::ps))

  tupleFromJSON [] _ (x :: xs)
    = throw (RedundantUples (JObject $ x::xs))

  tupleFromJSON (p :: ps) c ((l,r) :: xs)
    = case decEq (show c) l of
        No _ => throw (IllnumberedUple c l)
        Yes _ => do x <- fromJSON p r
                    xs <- tupleFromJSON ps (S c) xs
                    pure (x::xs)

  fieldsFromJSON : (prfs  : DList (String, Base) Marshable types)
                -> (rs    : List (String, JSON))
                         -> Capable (DList (String, Base) (Field Nil) types)
  fieldsFromJSON [] []
    = pure Nil

  fieldsFromJSON [] (x :: xs)
    = throw (RedundantFields (JObject (x::xs)))

  fieldsFromJSON (p :: ps) []
    = throw (MissingFields (p::ps))


  fieldsFromJSON (F lx p :: ps) ((ly,x) :: xs)
    = case decEq lx ly of
        No _ => throw (FieldMismatch lx ly)
        Yes Refl => do x <- fromJSON p x
                       xs <- fieldsFromJSON ps xs
                       pure (F lx x::xs)

  tagFromJSON : (prfs  : DList (String, Base) Marshable types)
             -> (label : String)
             -> (raw   : JSON)
                      -> Capable (DPair Base (\ty => (Elem (label,ty) types, Value Nil ty)))
  tagFromJSON prfs label raw
    = case Marshall.isElem label prfs of
        Nothing => throw (TagNot label)
        Just (type ** idx) => do let F label prf = lookup idx prfs
                                 x <- fromJSON prf raw
                                 pure (type ** (idx,x))

  fromJSON : {ty  : _}
          -> (prf : Marshable ty)
          -> (raw : JSON)
                 -> Capable (Value Nil ty)

  -- [ NOTE ] Chars are just single character strings...
  fromJSON CHAR (JString str)
    = maybe (mismatch CHAR (JString str))
            (pure . C)
            (toChar str)

  fromJSON STR (JString str)
    = pure (S str)

  fromJSON INT (JNumber n)
    = maybe (mismatch INT (JNumber n))
            (pure . I)
            (toInt n)

  fromJSON BOOL (JBoolean b)
    = pure (B b)

  fromJSON UNIT JNull
    = pure U

  fromJSON (LIST prf) (JArray rs)
    = do xs <- assert_total $ traverse (fromJSON prf) rs
         pure (MkList xs)

  fromJSON (VECTOR x n) (JArray rs)
    = vectorFromJSON x n n rs

  fromJSON (TUPLE x) (JObject rs)
    = do (x::y::zs) <- tupleFromJSON x 1 rs
           | _ => mismatch (TUPLE x) (JObject rs)
         pure (Tuple (x::y::zs))

  fromJSON (RECORD (p::ps)) (JObject rs)
    = do (f::fs) <- fieldsFromJSON (p::ps) rs
           | _ => mismatch (RECORD (p::ps)) (JObject rs)
         pure (Record (f::fs))

  fromJSON (UNION fields) (JObject [(l,raw)])
    = do (_ ** MkPair idx val) <- tagFromJSON fields l raw
         pure (Tag l idx val)

  fromJSON prf raw
    = mismatch prf raw


export
unmarshall : {ty  : _} -> (prf : Marshable ty)
          -> (raw : String)
                 -> Capable (Value Nil ty)
unmarshall prf str
  = maybe (throw (NotValidJSON str))
          (fromJSON prf)
          (JSON.parse str)

-- [ EOF ]
