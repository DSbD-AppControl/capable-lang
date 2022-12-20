||| Builtin Operations
|||
||| Covers:
|||   1. Builtin constants
|||   2. Operations on contant things.
|||   3. Memory & Process APIs
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Capable.Terms.Builtins

import public Data.List.Elem

import public Data.Fin

import Data.Vect

import System.File

import public Toolkit.Data.DList

import Capable.Terms.Types

%default total
%hide type

public export
data CharOpKind : (inputs  : Base)
           -> (returns : Base)
                      -> Type
  where
    Ord : CharOpKind CHAR INT
    Chr : CharOpKind INT  CHAR -- (UNION UNIT CHAR)
    Singleton : CharOpKind CHAR STR

public export
data BinOpIntKind = ADD | SUB | DIV | MUL

public export
data BinOpBoolKind = AND | OR

public export
data BinOpCmpKind = LT | LTE | EQ | GTE | GT

public export
data StringOpKind : (inputs  : List Base)
                 -> (returns : Base)
                            -> Type
  where
    Length : StringOpKind [STR]           INT
    Cons   : StringOpKind [CHAR, STR]     STR
    Slice  : StringOpKind [INT, INT, STR] STR

public export
data CmpTy : Base -> Type where
  CC : CmpTy CHAR
  CS : CmpTy STR
  CI : CmpTy INT
  CB : CmpTy BOOL

export
cmpTy : (b : Base) -> Maybe (CmpTy b)
cmpTy CHAR = Just CC
cmpTy STR  = Just CS
cmpTy INT  = Just CI
cmpTy BOOL = Just CB

cmpTy (ARRAY x k) = Nothing
cmpTy (TUPLE _)  = Nothing
cmpTy (UNION _) = Nothing
cmpTy (RECORD _) = Nothing
cmpTy UNIT        = Nothing
cmpTy (REF x)     = Nothing
cmpTy (HANDLE x)  = Nothing
cmpTy (FUNC xs x) = Nothing

||| Operations on constants
public export
data Builtin : (inputs : List Base)
           -> (return :      Base)
                     -> Type
  where
    -- ## Values
    U :           Builtin Nil UNIT
    C : Char   -> Builtin Nil CHAR
    S : String -> Builtin Nil STR
    I : Int    -> Builtin Nil INT
    B : Bool   -> Builtin Nil BOOL

    CharOp : CharOpKind i r
          -> Builtin [i] r

    StrOp : StringOpKind is r -> Builtin is r

    -- ## Int Ops
    BinOpInt : (operator : BinOpIntKind)
                        -> Builtin [INT, INT] INT

    -- ## Bool Ops
    BinOpBool : (operator : BinOpBoolKind)
                         -> Builtin [BOOL, BOOL] BOOL

    Not : Builtin [BOOL] BOOL

    Cmp : CmpTy type
       -> BinOpCmpKind
       -> Builtin [type, type] BOOL

    ToString : CmpTy type -> Builtin [type] STR

    -- ## Memory

    Fetch : Builtin [REF type]
                         type

    Alloc : Builtin [    type]
                    (REF type)

    Mutate : Builtin [ REF type, type]
                                 UNIT

    -- ## 'Process' API
    Open : (what : HandleKind)
        -> (m    : Mode)
                -> Builtin [STR]
                           (UNION (("left",INT) ::: [("right",HANDLE what)]))

    ReadLn : Builtin [HANDLE k]
                     (UNION (("left", INT) ::: [("right",STR)]))

    WriteLn : Builtin [HANDLE k, STR]
                      (UNION (("left", INT) ::: [("right", UNIT)]))

    Close : Builtin [HANDLE k]
                    UNIT

    -- ## Misc
    Print : Builtin [ STR ]
                      UNIT


-- [ EOF ]
