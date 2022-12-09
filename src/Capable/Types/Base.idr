||| Base types.
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
|||
module Capable.Types.Base

import Control.Function

import Decidable.Equality


import public Data.Vect
import public Data.List1
import public Data.List.Elem

import Text.PrettyPrint.Prettyprinter

import        Toolkit.Decidable.Do
import        Toolkit.Data.Vect.Extra

%default total

public export
data HandleKind = FILE | PROCESS

export
Show HandleKind where
  show FILE    = "FILE"
  show PROCESS = "PROCESS"

Uninhabited (FILE = PROCESS) where
  uninhabited Refl impossible

export
DecEq HandleKind where
  decEq FILE FILE
    = Yes Refl
  decEq FILE PROCESS
    = No absurd
  decEq PROCESS FILE
    = No (negEqSym absurd)
  decEq PROCESS PROCESS
    = Yes Refl

namespace Ty

  public export
  data Base : Type
    where
      CHAR,STR,INT,BOOL, UNIT : Base

      -- For file based IPC
      HANDLE : HandleKind -> Base

      -- Reference
      REF : Base -> Base

      ARRAY : Base -> Nat -> Base

      TUPLE : (fields : Vect (S (S n)) Base) -> Base

      RECORD : (fields : (List1 (String, Base)))
                       -> Base

      UNION : (fields : (List1 (String, Base)))
                       -> Base


      FUNC : (args : List Base)
          -> (ret  : Base)
                  -> Base

public export
data IsUnion : Base -> Type
  where
    U : IsUnion (UNION fs)

Uninhabited (IsUnion CHAR) where
  uninhabited U impossible

Uninhabited (IsUnion STR) where
  uninhabited U impossible

Uninhabited (IsUnion INT) where
  uninhabited U impossible

Uninhabited (IsUnion BOOL) where
  uninhabited U impossible

Uninhabited (IsUnion UNIT) where
  uninhabited U impossible

Uninhabited (IsUnion (HANDLE u)) where
  uninhabited U impossible

Uninhabited (IsUnion (REF u)) where
  uninhabited U impossible

Uninhabited (IsUnion (ARRAY x u)) where
  uninhabited U impossible

Uninhabited (IsUnion (TUPLE u)) where
  uninhabited U impossible

Uninhabited (IsUnion (RECORD u)) where
  uninhabited U impossible


Uninhabited (IsUnion (FUNC u us)) where
  uninhabited U impossible

export
isUnion : (base : Base) -> Dec (IsUnion base)
isUnion (UNION fields) = Yes U

isUnion CHAR            = No absurd
isUnion STR             = No absurd
isUnion INT             = No absurd
isUnion BOOL            = No absurd
isUnion UNIT            = No absurd
isUnion (HANDLE x)      = No absurd
isUnion (REF x)         = No absurd
isUnion (ARRAY x k)     = No absurd
isUnion (RECORD k)      = No absurd
isUnion (TUPLE fields)  = No absurd
isUnion (FUNC args ret) = No absurd

namespace Diag
  data Diag : (a,b : Base)
                  -> Type
    where
      UNIT : Diag UNIT UNIT
      CHAR : Diag CHAR CHAR
      STR  : Diag STR  STR
      INT  : Diag INT  INT
      BOOL : Diag BOOL BOOL

      HANDLE : (a,b : HandleKind)
                   -> Diag (HANDLE a) (HANDLE b)

      REF : (a,b : Base) -> Diag (REF a) (REF b)

      ARRAY : (a,b : Base)
           -> (x,y : Nat)
                  -> Diag (ARRAY a x)
                          (ARRAY b y)

      TUPLE : (xs : Vect (S (S n)) Base)
           -> (ys : Vect (S (S m)) Base)
                 -> Diag (TUPLE xs) (TUPLE ys)

      RECORD : (xs : List1 (String, Base))
            -> (ys : List1 (String, Base))
                  -> Diag (RECORD xs) (RECORD ys)

      UNION : (xs : List1 (String, Base))
           -> (ys : List1 (String, Base))
                 -> Diag (UNION xs) (UNION ys)

      FUNC : (xs, ys : List Base)
          -> (x , y  :      Base) -> Diag (FUNC xs x) (FUNC ys y)

  diag : (a,b : Base) -> Maybe (Diag a b)
  diag CHAR         CHAR        = Just CHAR
  diag STR          STR         = Just STR
  diag INT          INT         = Just INT
  diag BOOL         BOOL        = Just BOOL
  diag UNIT         UNIT        = Just UNIT
  diag (HANDLE x)   (HANDLE y)  = Just (HANDLE x y)
  diag (REF x)      (REF y)     = Just (REF x y)
  diag (ARRAY x k)  (ARRAY y l) = Just (ARRAY x y k l)
  diag (TUPLE xs)   (TUPLE ys)  = Just (TUPLE xs ys)
  diag (UNION xs)   (UNION ys)  = Just (UNION xs ys)
  diag (RECORD xs)  (RECORD ys) = Just (RECORD xs ys)
  diag (FUNC xs x)  (FUNC ys y) = Just (FUNC xs ys x y)

  diag _ _ = Nothing

  diagNot : (s : Base)
              -> Not (diag s s === Nothing)
  diagNot CHAR        = absurd
  diagNot STR         = absurd
  diagNot INT         = absurd
  diagNot BOOL        = absurd
  diagNot UNIT        = absurd
  diagNot (HANDLE _)  = absurd
  diagNot (REF _)     = absurd
  diagNot (ARRAY _ _) = absurd
  diagNot (TUPLE _)   = absurd
  diagNot (UNION _ )  = absurd
  diagNot (RECORD _ ) = absurd
  diagNot (FUNC _ _)  = absurd

  public export
  DecEq Base where
    decEq a@_ b@_ with (diag a b) proof eq

      _ | (Just UNIT) = Yes Refl
      _ | (Just CHAR) = Yes Refl
      _ | (Just STR) = Yes Refl
      _ | (Just INT) = Yes Refl
      _ | (Just BOOL) = Yes Refl

      _ | (Just (HANDLE x y))
        = decDo $ do Refl <- decEq x y `otherwise` (\Refl => Refl)
                     pure Refl

      _ | (Just (REF x y))
        = decDo $ do Refl <- decEq x y `otherwise` (\Refl => Refl)
                     pure Refl

      _ | (Just (ARRAY x y k j))
        = decDo $ do Refl <- decEq x y `otherwise` (\Refl => Refl)
                     Refl <- decEq k j `otherwise` (\Refl => Refl)
                     pure Refl

      _ | (Just (TUPLE xs ys))
        = decDo $ do Refl <- assert_total $ DiffLength.decEq xs ys `otherwise` (\Refl => Refl)
                     pure Refl
      _ | (Just (UNION xs ys))
        = decDo $ do Refl <- assert_total $ decEq xs ys `otherwise` (\Refl => Refl)
                     pure Refl

      _ | (Just (RECORD xs ys))
        = decDo $ do Refl <- assert_total $ decEq xs ys `otherwise` (\Refl => Refl)
                     pure Refl

      _ | (Just (FUNC xs ys x y))
        = decDo $ do Refl <- assert_total $ decEq xs ys `otherwise` (\Refl => Refl)
                     Refl <- decEq x y `otherwise` (\Refl => Refl)
                     pure Refl

      _ | Nothing = No (\Refl => diagNot _ eq)

export
toList : Vect q a -> List a
toList Nil = Nil
toList (x::xs) = x :: Base.toList xs

||| Variant of `encloseSep` with braces and comma as separator.
export
fields : List (Doc ann) -> Doc ann
fields = group . encloseSep (flatAlt (pretty "{ ") (pretty "{"))
                            (flatAlt (pretty " }") (pretty "}"))
                            (pretty "; ")

type : Base -> Doc ann
type CHAR
  = pretty "Char"

type STR
  = pretty "String"
type INT
  = pretty "Int"

type BOOL
  = pretty "Bool"

type UNIT
  = pretty "Unit"

type (HANDLE FILE)
  = pretty "File"
type (HANDLE PROCESS)
  = pretty "Process"

type (REF x)
  = group
  $ parens
  $ pretty "REF" <++> type x

type (ARRAY x k)
  = group
  $ brackets
  $ hcat
  [ type x
  , semi
  , pretty k
  ]

type (TUPLE xs)
  = tupled
  $ assert_total
  $ map type
  $ Base.toList xs

type (UNION xs)
  = group
  $ hsep
  [ pretty "union"
  , fields
  $ assert_total
  $ map (\(k,v) => group $ (hsep [pretty k, colon, type v]))
  $ forget xs
  ]

type (RECORD xs)
  = group
  $ hsep
  [ pretty "struct"
  , fields
  $ assert_total
  $ map (\(k,v) => group $ (hsep [pretty k, colon, type v]))
  $ forget xs
  ]

type (FUNC xs x)
  = group
  $ parens
  $ hsep
  $ punctuate (pretty "->")
  $ assert_total
  $ map type
  $ (xs ++ [x])

export
Pretty Base where
  pretty = type

export
Show Base where
  show = (show . annotate () . pretty)

-- [ EOF ]
