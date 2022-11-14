||| Base types.
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
|||
module Ola.Types.Base

import Control.Function

import Decidable.Equality

import public Data.Vect
import        Toolkit.Decidable.Do

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
  data Base = CHAR -- Char
          | STR  -- Strings
          | INT  -- Integers
          | BOOL -- Booleans

          | ARRAY Base Nat -- Arrays
          | PAIR  Base Base  -- Products
          | UNION Base Base  -- Sums

          | UNIT -- Unit

          | REF Base -- Reference

          | HANDLE HandleKind -- For file based IPC

          | FUNC (List Base) Base -- Functions

export
Biinjective ARRAY where
  biinjective Refl = (Refl, Refl)

export
Biinjective PAIR where
  biinjective Refl = (Refl, Refl)

export
Biinjective UNION where
  biinjective Refl = (Refl, Refl)


Uninhabited (CHAR = STR) where
  uninhabited Refl impossible

Uninhabited (CHAR = INT) where
  uninhabited Refl impossible

Uninhabited (CHAR = BOOL) where
  uninhabited Refl impossible

Uninhabited (CHAR = ARRAY ty n) where
  uninhabited Refl impossible

Uninhabited (CHAR = PAIR a b) where
  uninhabited Refl impossible

Uninhabited (CHAR = UNION a b) where
  uninhabited Refl impossible

Uninhabited (CHAR = UNIT) where
  uninhabited Refl impossible

Uninhabited (CHAR = REF ty) where
  uninhabited Refl impossible

Uninhabited (CHAR = HANDLE h) where
  uninhabited Refl impossible

Uninhabited (CHAR = FUNC a b) where
  uninhabited Refl impossible

-- Strings

Uninhabited (STR = INT) where
  uninhabited Refl impossible

Uninhabited (STR = BOOL) where
  uninhabited Refl impossible

Uninhabited (STR = ARRAY ty n) where
  uninhabited Refl impossible

Uninhabited (STR = PAIR a b) where
  uninhabited Refl impossible

Uninhabited (STR = UNION a b) where
  uninhabited Refl impossible

Uninhabited (STR = UNIT) where
  uninhabited Refl impossible

Uninhabited (STR = REF ty) where
  uninhabited Refl impossible

Uninhabited (STR = HANDLE h) where
  uninhabited Refl impossible

Uninhabited (STR = FUNC a b) where
  uninhabited Refl impossible

-- Integers

Uninhabited (INT = BOOL) where
  uninhabited Refl impossible

Uninhabited (INT = ARRAY ty n) where
  uninhabited Refl impossible

Uninhabited (INT = PAIR a b) where
  uninhabited Refl impossible

Uninhabited (INT = UNION a b) where
  uninhabited Refl impossible

Uninhabited (INT = UNIT) where
  uninhabited Refl impossible

Uninhabited (INT = REF ty) where
  uninhabited Refl impossible

Uninhabited (INT = HANDLE h) where
  uninhabited Refl impossible

Uninhabited (INT = FUNC a b) where
  uninhabited Refl impossible

-- Bool

Uninhabited (BOOL = ARRAY ty n) where
  uninhabited Refl impossible

Uninhabited (BOOL = PAIR a b) where
  uninhabited Refl impossible

Uninhabited (BOOL = UNION a b) where
  uninhabited Refl impossible

Uninhabited (BOOL = UNIT) where
  uninhabited Refl impossible

Uninhabited (BOOL = REF ty) where
  uninhabited Refl impossible

Uninhabited (BOOL = HANDLE h) where
  uninhabited Refl impossible

Uninhabited (BOOL = FUNC a b) where
  uninhabited Refl impossible

-- Array


Uninhabited (ARRAY ty n = PAIR a b) where
  uninhabited Refl impossible

Uninhabited (ARRAY ty n = UNION a b) where
  uninhabited Refl impossible

Uninhabited (ARRAY ty n = UNIT) where
  uninhabited Refl impossible

Uninhabited (ARRAY ty n = REF tyA) where
  uninhabited Refl impossible

Uninhabited (ARRAY ty n = HANDLE h) where
  uninhabited Refl impossible

Uninhabited (ARRAY ty n = FUNC a b) where
  uninhabited Refl impossible

-- Pair

Uninhabited (PAIR x y = UNION a b) where
  uninhabited Refl impossible

Uninhabited (PAIR x y = UNIT) where
  uninhabited Refl impossible

Uninhabited (PAIR x y = REF tyA) where
  uninhabited Refl impossible

Uninhabited (PAIR x y = HANDLE h) where
  uninhabited Refl impossible

Uninhabited (PAIR x y = FUNC a b) where
  uninhabited Refl impossible

-- Union

Uninhabited (UNION x y = UNIT) where
  uninhabited Refl impossible

Uninhabited (UNION x y = REF tyA) where
  uninhabited Refl impossible

Uninhabited (UNION x y = HANDLE h) where
  uninhabited Refl impossible

Uninhabited (UNION x y = FUNC a b) where
  uninhabited Refl impossible

-- Unit

Uninhabited (UNIT = REF tyA) where
  uninhabited Refl impossible

Uninhabited (UNIT = HANDLE h) where
  uninhabited Refl impossible

Uninhabited (UNIT = FUNC a b) where
  uninhabited Refl impossible

-- REF

Uninhabited (REF ty = HANDLE h) where
  uninhabited Refl impossible

Uninhabited (REF ty = FUNC a b) where
  uninhabited Refl impossible

-- Handle

Uninhabited (HANDLE h = FUNC a b) where
  uninhabited Refl impossible

export
DecEq Base where
  decEq CHAR b with (b)
    decEq CHAR b | CHAR
      = Yes Refl
    decEq CHAR b | STR         = No absurd
    decEq CHAR b | INT         = No absurd
    decEq CHAR b | BOOL        = No absurd
    decEq CHAR b | (ARRAY x k) = No absurd
    decEq CHAR b | (PAIR x y)  = No absurd
    decEq CHAR b | (UNION x y) = No absurd
    decEq CHAR b | UNIT        = No absurd
    decEq CHAR b | (REF x)     = No absurd
    decEq CHAR b | (HANDLE x)  = No absurd
    decEq CHAR b | (FUNC x y)  = No absurd

  decEq STR b with (b)
    decEq STR b | CHAR = No (negEqSym absurd)

    decEq STR b | STR = Yes Refl

    decEq STR b | INT         = No absurd
    decEq STR b | BOOL        = No absurd
    decEq STR b | (ARRAY x k) = No absurd
    decEq STR b | (PAIR x y)  = No absurd
    decEq STR b | (UNION x y) = No absurd
    decEq STR b | UNIT        = No absurd
    decEq STR b | (REF x)     = No absurd
    decEq STR b | (HANDLE x)  = No absurd
    decEq STR b | (FUNC x y)  = No absurd

  decEq INT b with (b)
    decEq INT b | CHAR = No (negEqSym absurd)
    decEq INT b | STR  = No (negEqSym absurd)

    decEq INT b | INT = Yes Refl

    decEq INT b | BOOL        = No absurd
    decEq INT b | (ARRAY x k) = No absurd
    decEq INT b | (PAIR x y)  = No absurd
    decEq INT b | (UNION x y) = No absurd
    decEq INT b | UNIT        = No absurd
    decEq INT b | (REF x)     = No absurd
    decEq INT b | (HANDLE x)  = No absurd
    decEq INT b | (FUNC x y)  = No absurd

  decEq BOOL b with (b)
    decEq BOOL b | CHAR = No (negEqSym absurd)
    decEq BOOL b | STR  = No (negEqSym absurd)
    decEq BOOL b | INT  = No (negEqSym absurd)

    decEq BOOL b | BOOL = Yes Refl

    decEq BOOL b | (ARRAY x k) = No absurd
    decEq BOOL b | (PAIR x y)  = No absurd
    decEq BOOL b | (UNION x y) = No absurd
    decEq BOOL b | UNIT        = No absurd
    decEq BOOL b | (REF x)     = No absurd
    decEq BOOL b | (HANDLE x)  = No absurd
    decEq BOOL b | (FUNC x y)  = No absurd

  decEq (ARRAY ty n) b with (b)
    decEq (ARRAY ty n) b | CHAR = No (negEqSym absurd)
    decEq (ARRAY ty n) b | STR  = No (negEqSym absurd)
    decEq (ARRAY ty n) b | INT  = No (negEqSym absurd)
    decEq (ARRAY ty n) b | BOOL = No (negEqSym absurd)

    decEq (ARRAY ty n) b | (ARRAY tyA nA)
      = decDo $ do Refl <- decEq ty tyA `otherwise` (\Refl => Refl)
                   Refl <- decEq n  nA  `otherwise` (\Refl => Refl)
                   pure Refl

    decEq (ARRAY ty n) b | (PAIR x y)  = No absurd
    decEq (ARRAY ty n) b | (UNION x y) = No absurd
    decEq (ARRAY ty n) b | UNIT        = No absurd
    decEq (ARRAY ty n) b | (REF x)     = No absurd
    decEq (ARRAY ty n) b | (HANDLE x)  = No absurd
    decEq (ARRAY ty n) b | (FUNC x y)  = No absurd

  decEq (PAIR x y) b with (b)
    decEq (PAIR x y) b | CHAR        = No (negEqSym absurd)
    decEq (PAIR x y) b | STR         = No (negEqSym absurd)
    decEq (PAIR x y) b | INT         = No (negEqSym absurd)
    decEq (PAIR x y) b | BOOL        = No (negEqSym absurd)
    decEq (PAIR x y) b | (ARRAY z k) = No (negEqSym absurd)

    decEq (PAIR x y) b | (PAIR z w)
      = decDo $ do Refl <- decEq x z `otherwise` (\Refl => Refl)
                   Refl <- decEq y w `otherwise` (\Refl => Refl)
                   pure Refl

    decEq (PAIR x y) b | (UNION z w) = No absurd
    decEq (PAIR x y) b | UNIT        = No absurd
    decEq (PAIR x y) b | (REF z)     = No absurd
    decEq (PAIR x y) b | (HANDLE z)  = No absurd
    decEq (PAIR x y) b | (FUNC z w)  = No absurd

  decEq (UNION x y) b with (b)
    decEq (UNION x y) b | CHAR        = No (negEqSym absurd)
    decEq (UNION x y) b | STR         = No (negEqSym absurd)
    decEq (UNION x y) b | INT         = No (negEqSym absurd)
    decEq (UNION x y) b | BOOL        = No (negEqSym absurd)
    decEq (UNION x y) b | (ARRAY z k) = No (negEqSym absurd)
    decEq (UNION x y) b | (PAIR z w)  = No (negEqSym absurd)

    decEq (UNION x y) b | (UNION z w)
      = decDo $ do Refl <- decEq x z `otherwise` (\Refl => Refl)
                   Refl <- decEq y w `otherwise` (\Refl => Refl)
                   pure Refl

    decEq (UNION x y) b | UNIT       = No absurd
    decEq (UNION x y) b | (REF z)    = No absurd
    decEq (UNION x y) b | (HANDLE z) = No absurd
    decEq (UNION x y) b | (FUNC z w) = No absurd

  decEq UNIT b with (b)
    decEq UNIT b | CHAR        = No (negEqSym absurd)
    decEq UNIT b | STR         = No (negEqSym absurd)
    decEq UNIT b | INT         = No (negEqSym absurd)
    decEq UNIT b | BOOL        = No (negEqSym absurd)
    decEq UNIT b | (ARRAY x k) = No (negEqSym absurd)
    decEq UNIT b | (PAIR x y)  = No (negEqSym absurd)
    decEq UNIT b | (UNION x y) = No (negEqSym absurd)

    decEq UNIT b | UNIT = Yes Refl

    decEq UNIT b | (REF x)    = No absurd
    decEq UNIT b | (HANDLE x) = No absurd
    decEq UNIT b | (FUNC x y) = No absurd

  decEq (REF x) b with (b)
    decEq (REF x) b | CHAR        = No (negEqSym absurd)
    decEq (REF x) b | STR         = No (negEqSym absurd)
    decEq (REF x) b | INT         = No (negEqSym absurd)
    decEq (REF x) b | BOOL        = No (negEqSym absurd)
    decEq (REF x) b | (ARRAY y k) = No (negEqSym absurd)
    decEq (REF x) b | (PAIR y z)  = No (negEqSym absurd)
    decEq (REF x) b | (UNION y z) = No (negEqSym absurd)
    decEq (REF x) b | UNIT        = No (negEqSym absurd)

    decEq (REF x) b | (REF y)
      = decDo $ do Refl <- decEq x y `otherwise` (\Refl => Refl)
                   pure Refl

    decEq (REF x) b | (HANDLE y) = No absurd
    decEq (REF x) b | (FUNC y z) = No absurd

  decEq (HANDLE x) b with (b)
    decEq (HANDLE x) b | CHAR        = No (negEqSym absurd)
    decEq (HANDLE x) b | STR         = No (negEqSym absurd)
    decEq (HANDLE x) b | INT         = No (negEqSym absurd)
    decEq (HANDLE x) b | BOOL        = No (negEqSym absurd)
    decEq (HANDLE x) b | (ARRAY y k) = No (negEqSym absurd)
    decEq (HANDLE x) b | (PAIR y z)  = No (negEqSym absurd)
    decEq (HANDLE x) b | (UNION y z) = No (negEqSym absurd)
    decEq (HANDLE x) b | UNIT        = No (negEqSym absurd)
    decEq (HANDLE x) b | (REF y)     = No (negEqSym absurd)

    decEq (HANDLE x) b | (HANDLE y)
      = decDo $ do Refl <- decEq x y `otherwise` (\Refl => Refl)
                   pure Refl

    decEq (HANDLE x) b | (FUNC y z) = No absurd

  decEq (FUNC x y) b with (b)
    decEq (FUNC x y) b | CHAR        = No (negEqSym absurd)
    decEq (FUNC x y) b | STR         = No (negEqSym absurd)
    decEq (FUNC x y) b | INT         = No (negEqSym absurd)
    decEq (FUNC x y) b | BOOL        = No (negEqSym absurd)
    decEq (FUNC x y) b | (ARRAY z k) = No (negEqSym absurd)
    decEq (FUNC x y) b | (PAIR z w)  = No (negEqSym absurd)
    decEq (FUNC x y) b | (UNION z w) = No (negEqSym absurd)
    decEq (FUNC x y) b | UNIT        = No (negEqSym absurd)
    decEq (FUNC x y) b | (REF z)     = No (negEqSym absurd)
    decEq (FUNC x y) b | (HANDLE z)  = No (negEqSym absurd)

    decEq (FUNC x y) b | (FUNC z w)
      = decDo $ do Refl <- assert_total $ decEq x z `otherwise` (\Refl => Refl)
                   -- @TODO Check if above is okay.
                   Refl <- decEq y w `otherwise` (\Refl => Refl)
                   pure Refl


export
Show Ty.Base where
  show CHAR        = "CHAR"
  show STR         = "STR"
  show INT         = "INT"
  show BOOL        = "BOOL"
  show (ARRAY x k) = "(ARRAY \{show x} \{show k})"
  show (PAIR x y)  = "(PAIR \{show x} \{show y})"
  show (UNION x y) = "(UNION \{show x} \{show y})"
  show UNIT        = "UNIT"
  show (REF x)     = "(REF \{show x})"
  show (HANDLE x)  = "(HANDLE \{show x})"
  show (FUNC x y)  = "(\{(assert_total $ show x)} -> \{show y}) "
-- [ EOF ]
