||| Module    : Main.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
||| Borrowed From Idris2 and improved with Test.Unit
module Main

import Data.List

import Test.Golden

%default total

tests : TestPool
tests
  = MkTestPool "Some Tests"
        []
        Nothing
        [ "000-todo"
        , "001-basics"
        , "002-roles"
        ]

files : IO TestPool
files
  = testsInDir "files"
               (const True)
               "File Handling"
               []
               Nothing

examples : IO TestPool
examples
  = testsInDir "examples"
               (const True)
               "Working examples"
               []
               Nothing

covering
main : IO ()
main
  = runner [ tests
           , !files
           , !examples
           ]

-- [ EOF ]
