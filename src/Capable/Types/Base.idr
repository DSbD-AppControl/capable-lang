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
import public Data.Vect.Quantifiers
import public Data.List.Quantifiers

import Text.PrettyPrint.Prettyprinter

import        Toolkit.Decidable.Do
import        Toolkit.Decidable.Informative
import        Toolkit.Data.DList
import        Toolkit.Data.DVect
import        Toolkit.Data.Vect.Extra

%default total

namespace HandleKind
  public export
  data HandleKind = FILE | PROCESS | PIPE

  export
  Show HandleKind where
    show FILE    = "FILE"
    show PROCESS = "PROCESS"
    show PIPE    = "PIPE"

  Uninhabited (FILE = PROCESS) where
    uninhabited Refl impossible

  Uninhabited (FILE = PIPE) where
    uninhabited Refl impossible

  Uninhabited (PIPE = PROCESS) where
    uninhabited Refl impossible

  data Diag : (a,b : HandleKind)
                  -> Type
    where
      F  : Diag FILE FILE
      PR : Diag PROCESS PROCESS
      PI : Diag PIPE    PIPE


  diag : (a,b : HandleKind) -> Maybe (Diag a b)
  diag FILE    FILE    = Just F
  diag PROCESS PROCESS = Just PR
  diag PIPE    PIPE = Just PI

  diag _ _ = Nothing

  diagNot : (s : HandleKind)
              -> Not (diag s s === Nothing)
  diagNot FILE    = absurd
  diagNot PROCESS = absurd
  diagNot PIPE    = absurd


  export
  DecEq HandleKind where

    decEq a@_ b@_ with (diag a b) proof eq

      _ | (Just F) = Yes Refl
      _ | (Just PR) = Yes Refl
      _ | (Just PI) = Yes Refl

      _ | Nothing = No (\Refl => diagNot _ eq)

namespace Ty

  public export
  data Base : Type
    where
      CHAR,STR,INT,BOOL, UNIT : Base

      -- For file based IPC
      HANDLE : HandleKind -> Base

      -- Reference
      REF : Base -> Base

      VECTOR : Base -> Nat -> Base
      LIST : Base -> Base

      TUPLE : (fields : Vect (S (S n)) Base) -> Base

      RECORD : (fields : (List1 (String, Base)))
                       -> Base

      UNION : (fields : (List1 (String, Base)))
                       -> Base

  public export
  EITHER : (a,b : Base) -> Base
  EITHER a b
    = UNION
    $ ("left", a)
    ::: [MkPair "right" b]

  public export
  POPEN2 : Base
  POPEN2 = HANDLE PROCESS

  public export
  data Iterable : Base -> Base -> Type where
    L : Iterable (LIST ty)     ty
    V : {s : _} -> Iterable (VECTOR ty s) ty


  Uninhabited (DPair Base (Iterable CHAR       )) where uninhabited (typw ** L) impossible
  Uninhabited (DPair Base (Iterable STR        )) where uninhabited (typw ** L) impossible
  Uninhabited (DPair Base (Iterable INT        )) where uninhabited (typw ** L) impossible
  Uninhabited (DPair Base (Iterable BOOL       )) where uninhabited (typw ** L) impossible
  Uninhabited (DPair Base (Iterable UNIT       )) where uninhabited (typw ** L) impossible
  Uninhabited (DPair Base (Iterable (HANDLE k) )) where uninhabited (typw ** L) impossible
  Uninhabited (DPair Base (Iterable (REF f)    )) where uninhabited (typw ** L) impossible
  Uninhabited (DPair Base (Iterable (RECORD fs))) where uninhabited (typw ** L) impossible
  Uninhabited (DPair Base (Iterable (UNION fs) )) where uninhabited (typw ** L) impossible
  Uninhabited (DPair Base (Iterable (TUPLE fs) )) where uninhabited (typw ** L) impossible

  export
  isIterable : (ty : Base)
                  -> Dec (DPair Base (Iterable ty))
  isIterable (VECTOR x k)
    = Yes (x ** V)
  isIterable (LIST x)
    = Yes (x ** L)

  isIterable CHAR
    = No absurd
  isIterable STR
    = No absurd
  isIterable INT
    = No absurd
  isIterable BOOL
    = No absurd
  isIterable UNIT
    = No absurd
  isIterable (HANDLE x)
    = No absurd
  isIterable (REF x)
    = No absurd
  isIterable (TUPLE fields)
    = No absurd
  isIterable (RECORD fields)
    = No absurd
  isIterable (UNION fields)
    = No absurd

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

      VECTOR : (a,b : Base)
           -> (x,y : Nat)
                  -> Diag (VECTOR a x)
                          (VECTOR b y)

      LIST : (a,b : Base)
                 -> Diag (LIST a)
                         (LIST b)

      TUPLE : (xs : Vect (S (S n)) Base)
           -> (ys : Vect (S (S m)) Base)
                 -> Diag (TUPLE xs) (TUPLE ys)

      RECORD : (xs : List1 (String, Base))
            -> (ys : List1 (String, Base))
                  -> Diag (RECORD xs) (RECORD ys)

      UNION : (xs : List1 (String, Base))
           -> (ys : List1 (String, Base))
                 -> Diag (UNION xs) (UNION ys)

  diag : (a,b : Base) -> Maybe (Diag a b)
  diag CHAR         CHAR        = Just CHAR
  diag STR          STR         = Just STR
  diag INT          INT         = Just INT
  diag BOOL         BOOL        = Just BOOL
  diag UNIT         UNIT        = Just UNIT
  diag (HANDLE x)   (HANDLE y)  = Just (HANDLE x y)
  diag (REF x)      (REF y)     = Just (REF x y)
  diag (VECTOR x k)  (VECTOR y l) = Just (VECTOR x y k l)
  diag (LIST a)     (LIST b)      = Just (LIST a b)
  diag (TUPLE xs)   (TUPLE ys)  = Just (TUPLE xs ys)
  diag (UNION xs)   (UNION ys)  = Just (UNION xs ys)
  diag (RECORD xs)  (RECORD ys) = Just (RECORD xs ys)
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
  diagNot (VECTOR _ _) = absurd
  diagNot (LIST _)    = absurd
  diagNot (TUPLE _)   = absurd
  diagNot (UNION _ )  = absurd
  diagNot (RECORD _ ) = absurd

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

      _ | (Just (VECTOR x y k j))
        = decDo $ do Refl <- decEq x y `otherwise` (\Refl => Refl)
                     Refl <- decEq k j `otherwise` (\Refl => Refl)
                     pure Refl

      _ | (Just (LIST x y))
        = decDo $ do Refl <- decEq x y `otherwise` (\Refl => Refl)
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

--      _ | (Just (FUNC xs ys x y))
--        = decDo $ do Refl <- assert_total $ decEq xs ys `otherwise` (\Refl => Refl)
--                     Refl <- decEq x y `otherwise` (\Refl => Refl)
--                     pure Refl

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
type (HANDLE PIPE)
  = pretty "Pipe"

type (REF x)
  = group
  $ parens
  $ pretty "REF" <++> type x

type (VECTOR x k)
  = group
  $ brackets
  $ hcat
  [ type x
  , semi
  , pretty k
  ]

type (LIST x)
  = group
  $ brackets
  $ type x


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

--type (FUNC xs x)
--  = group
--  $ parens
--  $ hsep
--  $ punctuate (pretty "->")
--  $ assert_total
--  $ map type
--  $ (xs ++ [x])

export
Pretty Base where
  pretty = type

export
Show Base where
  show = (show . annotate () . pretty)


mutual
  ||| [ NOTE ] Can a datatype be marshalled to/from wires.
  namespace Marshall
    namespace Field
      public export
      data Marshable : (str : (String, Base)) -> Type where
        F : (s : String) -> Marshable ty -> Marshable (s, ty)

      public export
      data MarshableNot : (str : (String, Base)) -> Type where
        FNot : (str : String)
            -> (prf : MarshableNot ty)
                   -> MarshableNot (str, ty)

    public export
    data Marshable : (type : Base) -> Type where
      CHAR  : Marshable CHAR
      STR   : Marshable STR
      INT   : Marshable INT
      BOOL  : Marshable BOOL
      UNIT  : Marshable UNIT

      VECTOR : Marshable ty -> (n : Nat) -> Marshable (VECTOR ty n)

      LIST : Marshable ty -> Marshable (LIST ty)

      TUPLE : DVect Base Marshable (S (S n)) types -> Marshable (TUPLE types)

      RECORD : (fields : DList (String, Base) Marshable (f::fs))
                      -> Marshable (RECORD (f:::fs))

      UNION : (fields : DList (String, Base) Marshable (f::fs))
                     -> Marshable (UNION (f:::fs))

    public export
    data MarshableNot : (type : Base) -> Type where
      REF : MarshableNot (REF r)
      HANDLE : MarshableNot (HANDLE r)

      LISTNot : MarshableNot ty -> MarshableNot (LIST ty)

      VECTORNot : (prf : MarshableNot ty )
              -> (n   : Nat)
                     -> MarshableNot (VECTOR ty n)

      TUPLENot : (prf : Any MarshableNot types)
                     -> MarshableNot (TUPLE types)

      RECORDNot : (prf : Any MarshableNot (f::fs))
                      -> MarshableNot (RECORD (f:::fs))

      UNIONNot : (prf : Any MarshableNot (f::fs))
                     -> MarshableNot (UNION (f:::fs))

mutual
  namespace Marshall
    namespace Tuple
      public export
      decEq : (as : DVect Base Marshable n a)
           -> (bs : DVect Base Marshable m b)
           -> (n = m)
           -> (a = b)
           -> Equal as bs
      decEq [] [] Refl Refl = Refl
      decEq (ex :: rest) (x :: y) Refl Refl
        = case decEq ex x Refl of
            Refl =>
              case decEq rest y Refl Refl of
                Refl => Refl

    namespace Fields
      public export
      decEq : (as : DList (String,Base) Marshable a)
           -> (bs : DList (String,Base) Marshable b)
           -> (a = b)
           -> Equal as bs
      decEq [] [] Refl = Refl
      decEq ((F l ex) :: rest) ((F l x) :: y) Refl
        = case decEq ex x Refl of
            Refl =>
              case decEq rest y Refl of
                Refl => Refl

    public export
    decEq : (a : Marshall.Marshable tyA)
         -> (b : Marshall.Marshable tyB)
         -> (prf : tyA = tyB)
         -> Equal a b
    decEq CHAR CHAR Refl = Refl
    decEq STR STR Refl   = Refl
    decEq INT INT Refl   = Refl
    decEq BOOL BOOL Refl = Refl
    decEq UNIT UNIT Refl = Refl

    decEq (VECTOR y n) (VECTOR x n) Refl
      = case decEq y x Refl of
         Refl => Refl

    decEq (LIST y) (LIST x) Refl
      = case decEq y x Refl of
         Refl => Refl

    decEq (TUPLE y) (TUPLE x) Refl
      = case decEq y x Refl Refl of
          Refl => Refl

    decEq (RECORD x) (RECORD fields) Refl
      = case decEq x fields Refl of
          Refl => Refl
    decEq (UNION x) (UNION fields) Refl
      = case decEq x fields Refl of
             Refl => Refl


namespace Marshall
  export
  mkPretty : Marshall.Marshable ty -> Doc ann
  mkPretty CHAR = pretty "Char"
  mkPretty STR  = pretty "String"
  mkPretty INT  = pretty "Int"
  mkPretty BOOL = pretty "Bool"
  mkPretty UNIT = pretty "Unit"
  mkPretty (VECTOR x n)
    = group
    $ brackets
    $ hcat
    [ mkPretty x
    , semi
    , pretty n
    ]

  mkPretty (LIST x)
    = group
    $ brackets
    $ mkPretty x

  mkPretty (TUPLE xs)
    = tupled
    $ assert_total
    $ Base.toList
    $ mapToVect mkPretty xs

  mkPretty (RECORD fs)
    = group
    $ hsep
    [ pretty "struct"
    , fields
    $ assert_total
    $ mapToList (\(F k v) => group $ (hsep [pretty k, colon, mkPretty v]))
                fs
    ]

  mkPretty (UNION fs)
    = group
    $ hsep
    [ pretty "union"
    , fields
    $ assert_total
    $ mapToList (\(F k v) => group $ (hsep [pretty k, colon, mkPretty v])) fs
    ]

  export
  Pretty (Marshall.Marshable ty) where
    pretty = mkPretty

  export
  Show (Marshall.Marshable ty) where
    show = (show . annotate () . pretty)

  prettyNot : Marshall.MarshableNot ty -> Doc ann
  prettyNot REF
    = pretty "Is a Reference."

  prettyNot HANDLE
    = pretty "Is a handle."

  prettyNot (LISTNot prf)
    = pretty "Contains a Reference/Handle"

  prettyNot (VECTORNot prf n)
    = pretty "Contains a Reference/Handle"
  prettyNot (TUPLENot prf)
    = pretty "Contains a Reference/Handle"
  prettyNot (RECORDNot prf)
    = pretty "Contains a Reference/Handle"
  prettyNot (UNIONNot prf)
    = pretty "Contains a Reference/Handle"

  export
  Pretty (Marshall.MarshableNot ty) where
    pretty = prettyNot

  export
  Show (Marshall.MarshableNot ty) where
    show = (show . annotate () . pretty)

namespace Marshall
  export
  Uninhabited (Marshable (HANDLE ty)) where
    uninhabited CHAR impossible

  export
  Uninhabited (Marshable (REF ty)) where
    uninhabited CHAR impossible

mutual
  namespace Marshall
    namespace Field
      export
      marshable : (kv : Pair String Base)
                     -> DecInfo (MarshableNot kv)
                                (Marshable    kv)
      marshable (str, ty) with (marshable ty)
        marshable (str, ty) | (Yes prf)
          = Yes (F str prf)
        marshable (str, ty) | (No prf no)
          = No (FNot str prf) (\(F s prf) => no prf)

    namespace Tuples
      export
      marshable : (fields : Vect n Base)
                         -> DecInfo (Any        MarshableNot   fields)
                                    (DVect Base Marshable    n fields)

      -- [ NOTE ] This is okay, the input will _always_ be minimum length two.
      marshable []
        = Yes []

      marshable (x :: xs) with (marshable x)
        marshable (x :: xs) | (Yes p) with (marshable xs)
          marshable (x :: xs) | (Yes p) | (Yes ps)
            = Yes (p :: ps)
          marshable (x :: xs) | (Yes p) | (No prf no)
            = No (There prf)
                 (\case (ex :: rest) => no rest)

        marshable (x :: xs) | (No prf no)
          = No (Here prf)
               (\case (ex :: rest) => no ex)

    namespace Fields
      export
      marshable : (fields : List (String, Base))
                         -> DecInfo (Any                  MarshableNot fields)
                                    (DList (String, Base) Marshable    fields)
      -- [ NOTE ] This is okay, as the input will _always_ be minimum length one.
      marshable []
        = Yes []
      marshable (x :: xs) with (marshable x)
        marshable (x :: xs) | (Yes p) with (marshable xs)
          marshable (x :: xs) | (Yes p) | (Yes ps)
            = Yes (p :: ps)

          marshable (x :: xs) | (Yes p) | (No prf no)
            = No (There prf) (\case (elem :: rest) => no rest)

        marshable (x :: xs) | (No prf no)
          = No (Here prf) (\case (elem :: rest) => no elem)

    export
    marshable : (type : Base)
                     -> DecInfo (MarshableNot type)
                                (Marshable    type)
    marshable CHAR
      = Yes CHAR
    marshable STR
      = Yes STR
    marshable INT
      = Yes INT
    marshable BOOL
      = Yes BOOL
    marshable UNIT
      = Yes UNIT

    marshable (HANDLE x)
      = No HANDLE absurd

    marshable (REF x)
      = No REF absurd

    marshable (LIST ty) with (marshable ty)
      marshable (LIST ty) | (Yes prf)
        = Yes (LIST prf)
      marshable (LIST ty) | (No prf no)
        = No (LISTNot prf)
             (\case (LIST x) => no x)

    marshable (VECTOR ty n) with (marshable ty)
      marshable (VECTOR ty n) | (Yes prf)
        = Yes (VECTOR prf n)
      marshable (VECTOR ty n) | (No prf no)
        = No (VECTORNot prf n)
             (\case (VECTOR x n) => no x)

    marshable (TUPLE fields) with (marshable fields)
      marshable (TUPLE fields) | (Yes prf)
        = Yes (TUPLE prf)

      marshable (TUPLE fields) | (No prf no)
        = No (TUPLENot prf)
             (\case (TUPLE x) => no x)

    marshable (RECORD (head ::: tail)) with (marshable (head::tail))
      marshable (RECORD (head ::: tail)) | (Yes prf)
        = Yes (RECORD prf)
      marshable (RECORD (head ::: tail)) | (No prf no)
        = No (RECORDNot prf) (\case (RECORD fields) => no fields)

    marshable (UNION (head ::: tail)) with (marshable (head::tail))
      marshable (UNION (head ::: tail)) | (Yes prf)
        = Yes (UNION prf)
      marshable (UNION (head ::: tail)) | (No prf no)
        = No (UNIONNot prf) (\case (UNION fields) => no fields)

namespace IsUnion
  public export
  data IsUnion : Base -> Type
    where
      U : (fields : DList (String, Base) Marshable (f::fs))
                 -> IsUnion (UNION (f:::fs))

  public export
  data IsUnionNot : Base -> Type
    where
      CHAR  : IsUnionNot CHAR
      STR   : IsUnionNot STR
      INT   : IsUnionNot INT
      BOOL  : IsUnionNot BOOL
      UNIT  : IsUnionNot UNIT

      HANDLE : IsUnionNot (HANDLE ref)
      REF    : IsUnionNot (REF ref)

      LIST : IsUnionNot (LIST ty)

      VECTOR : IsUnionNot (VECTOR ty n)

      TUPLE : IsUnionNot (TUPLE types)

      RECORD : IsUnionNot (RECORD fs)

      UNIONNot : (prf : Any MarshableNot (f::fs))
                     -> IsUnionNot (UNION (f:::fs))


  Uninhabited (IsUnion CHAR) where
    uninhabited (U _) impossible

  Uninhabited (IsUnion STR) where
    uninhabited (U _) impossible

  Uninhabited (IsUnion INT) where
    uninhabited (U _) impossible

  Uninhabited (IsUnion BOOL) where
    uninhabited (U _) impossible

  Uninhabited (IsUnion UNIT) where
    uninhabited (U _) impossible

  Uninhabited (IsUnion (HANDLE u)) where
    uninhabited (U _) impossible

  Uninhabited (IsUnion (REF u)) where
    uninhabited (U _) impossible

  Uninhabited (IsUnion (LIST x)) where
    uninhabited (U _) impossible

  Uninhabited (IsUnion (VECTOR x u)) where
    uninhabited (U _) impossible

  Uninhabited (IsUnion (TUPLE u)) where
    uninhabited (U _) impossible

  Uninhabited (IsUnion (RECORD u)) where
    uninhabited (U _) impossible

  --Uninhabited (IsUnion (FUNC u us)) where
  --  uninhabited (U _) impossible

  export
  isUnion : (base : Base) -> DecInfo (IsUnionNot base) (IsUnion base)
  isUnion (UNION (head ::: tail)) with (marshable (head::tail))
    isUnion (UNION (head ::: tail)) | (Yes prf)
      = Yes (U prf)
    isUnion (UNION (head ::: tail)) | (No prf no)
      = No (UNIONNot prf)
           (\case (U fields) => no fields)


  isUnion CHAR            = No CHAR   absurd
  isUnion STR             = No STR    absurd
  isUnion INT             = No INT    absurd
  isUnion BOOL            = No BOOL   absurd
  isUnion UNIT            = No UNIT   absurd
  isUnion (HANDLE x)      = No HANDLE absurd
  isUnion (REF x)         = No REF    absurd
  isUnion (LIST x)        = No LIST   absurd
  isUnion (VECTOR x k)    = No VECTOR  absurd
  isUnion (RECORD k)      = No RECORD absurd
  isUnion (TUPLE fields)  = No TUPLE  absurd
  --isUnion (FUNC args ret) = No absurd

-- [ EOF ]
