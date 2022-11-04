||| Builtins
|||
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
module Ola.Terms.Builtins

import Data.List.Elem

import public Data.Fin

import Data.Vect

import System.File

import public Toolkit.Data.DList

import Ola.Terms.Types

%default total

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

    -- @TODO primitive operations on char
    -- @TODO primitive operations on str
    -- @TODO primitive operations on Int
    -- @TODO primitive operations on bool

    -- ## Memory

    Fetch : Builtin [REF type]
                         type

    Alloc : Builtin [    type]
                    (REF type)

    -- ## 'Process' API
    Open : (what : HandleKind)
        -> (m    : Mode)
                -> Builtin [STR]
                           (UNION INT (HANDLE what))

    ReadLn : Builtin [HANDLE k]
                     (UNION INT STR)

    WriteLn : Builtin [HANDLE k, STR]
                      (UNION INT UNIT)

    Close : Builtin [HANDLE k]
                    UNIT
