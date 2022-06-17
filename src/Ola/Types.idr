module Ola.Types

%default total

public export
data HandleKind = FILE | PROCESS

public export
data Ty = CHAR -- Char
        | STR  -- Strings
        | INT  -- Integers
        | BOOL -- Booleans

        | ARRAY Ty Nat -- Arrays
        | PAIR  Ty Ty  -- Products
        | UNION Ty Ty  -- Sums

        | UNIT -- Unit

        | REF Ty -- Reference

        | HANDLE HandleKind -- For file based IPC

        | FUNC Ty Ty -- Functions


-- [ EOF ]
