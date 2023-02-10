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

import public Data.Singleton

import public System.File

import Language.JSON
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

unmarshable : (ty : Base) -> (prf : MarshableNot ty) -> Capable a
unmarshable ty prf = throw (NotMarshable ty prf)

mismatch : (ty : Base) -> (prf : Marshable ty) -> (raw : JSON)
              -> Capable a
mismatch ty prf raw = throw (Mismatch ty prf raw)

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

  arrayToJSON : (value : Value store (ARRAY ty n) )
             -> (prf   : Marshable ty)
                      -> List JSON
  arrayToJSON ArrayEmpty prf
    = Nil
  arrayToJSON (ArrayCons x y) prf
    =    let x  = toJSON x prf
      in let xs = arrayToJSON y prf
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

  toJSON val (ARRAY ty n)
    =    let n  = (JNumber (cast n))
      in let xs = arrayToJSON val ty

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
marshall : (prf : Marshable ty)
        -> (val : Value store ty)
               -> Capable JSON
marshall prf val = pure (toJSON val prf)

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
      -> (xs     : List (String, Base))
                -> Maybe (DPair Base (\x => Elem (s,x) xs))
isElem s []
  = Nothing
isElem s ((s',x) :: xs)
  = case decEq s s' of
      No _ => do (x' ** prf) <- isElem s xs
                 pure (x' ** There prf)
      Yes Refl => pure (x ** Here)

mutual

  arrayFromJSON : (ty  : Base)
               -> (prf : Marshable ty)
               -> (x   : Nat)
               -> (nat : Nat)
               -> (rs  : List JSON)
                      -> Capable (Value Nil (ARRAY ty nat))
  arrayFromJSON ty prf _ 0 []
    = pure ArrayEmpty

  arrayFromJSON ty prf n (S k) []
    = throw (MissingElems (S k) (ARRAY ty n) (ARRAY prf n))

  arrayFromJSON ty prf n 0 (x :: xs)
    = throw (RedundantElems (ARRAY ty n)
                            (ARRAY prf n)
                            (JArray (x::xs)))

  arrayFromJSON ty prf n (S k) (x :: xs)
    = do x <- fromJSON ty prf x
         xs <- arrayFromJSON ty prf n k xs
         pure (ArrayCons x xs)


  tupleFromJSON : (types : Vect n Base)
               -> (prfs  : DVect Base Marshable n types)
               -> (c     : Nat)
               -> (rs    : List (String, JSON))
                        -> Capable (DVect Base (Value Nil) n types)
  tupleFromJSON [] [] _ []
    = pure Nil

  tupleFromJSON (x :: xs) (p :: ps) _ []
    = throw (MissingUples (x::xs) (p::ps))

  tupleFromJSON [] [] _ (x :: xs)
    = throw (RedundantUples (JObject $ x::xs))

  tupleFromJSON (t :: ts) (p :: ps) c ((l,r) :: xs)
    = case decEq (show c) l of
        No _ => throw (IllnumberedUple c l)
        Yes _ => do x <- fromJSON t p r
                    xs <- tupleFromJSON ts ps (S c) xs
                    pure (x::xs)

  fieldsFromJSON : (types : List (String, Base))
                -> (prfs  : DList (String, Base) Marshable types)
                -> (rs    : List (String, JSON))
                         -> Capable (DList (String, Base) (Field Nil) types)
  fieldsFromJSON [] [] []
    = pure Nil

  fieldsFromJSON [] [] (x :: xs)
    = throw (RedundantFields (JObject (x::xs)))

  fieldsFromJSON (t :: ts) (p :: ps) []
    = throw (MissingFields (t::ts) (p::ps))


  fieldsFromJSON ((lx,t) :: ts) (F lx p :: ps) ((ly,x) :: xs)
    = case decEq lx ly of
        No _ => throw (FieldMismatch lx ly)
        Yes Refl => do x <- fromJSON t p x
                       xs <- fieldsFromJSON ts ps xs
                       pure (F lx x::xs)

  tagFromJSON : (types : List (String, Base))
             -> (prfs  : DList (String, Base) Marshable types)
             -> (label : String)
             -> (raw   : JSON)
                      -> Capable (DPair Base (\ty => (Elem (label,ty) types, Value Nil ty)))
  tagFromJSON types prfs label raw
    = case Marshall.isElem label types of
        Nothing => throw (TagNot label)
        Just (type ** idx) => do let F label prf = lookup idx prfs
                                 x <- fromJSON type prf raw
                                 pure (type ** (idx,x))

  fromJSON : (ty  : Base)
          -> (prf : Marshable ty)
          -> (raw : JSON)
                 -> Capable (Value Nil ty)

  -- [ NOTE ] Chars are just single character strings...
  fromJSON CHAR CHAR (JString str)
    = maybe (mismatch CHAR CHAR (JString str))
            (pure . C)
            (toChar str)

  fromJSON STR STR (JString str)
    = pure (S str)

  fromJSON INT INT (JNumber n)
    = maybe (mismatch INT INT (JNumber n))
            (pure . I)
            (toInt n)

  fromJSON BOOL BOOL (JBoolean b)
    = pure (B b)

  fromJSON UNIT UNIT JNull
    = pure U

  fromJSON (ARRAY ty n) (ARRAY x n) (JArray rs)
    = arrayFromJSON ty x n n rs

  fromJSON (TUPLE types) (TUPLE x) (JObject rs)
    = do (x::y::zs) <- tupleFromJSON types x 1 rs
           | _ => mismatch (TUPLE types) (TUPLE x) (JObject rs)
         pure (Tuple (x::y::zs))

  fromJSON (RECORD (f ::: fs)) (RECORD (p::ps)) (JObject rs)
    = do (f::fs) <- fieldsFromJSON (f::fs) (p::ps) rs
           | _ => mismatch (RECORD (f ::: fs)) (RECORD (p::ps)) (JObject rs)
         pure (Record (f::fs))

  fromJSON (UNION (f ::: fs)) (UNION fields) (JObject [(l,raw)])
    = do (_ ** MkPair idx val) <- tagFromJSON (f::fs) fields l raw
         pure (Tag l idx val)

  fromJSON ty prf raw
    = mismatch ty prf raw


export
unmarshall : (ty  : Base)
          -> (prf : Marshable ty)
          -> (raw : JSON)
                 -> Capable (Value Nil ty)
unmarshall
  = fromJSON

-- [ EOF ]
