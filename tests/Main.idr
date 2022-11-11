||| Module    : Main.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
||| Borrowed From Idris2 and improved with Test.Unit
module Main

import Data.List

import Test.Golden

%default total

mkPool : (dirName, poolName : String)
                           -> IO TestPool
mkPool d p
  = testsInDir d (const True)
               p [] Nothing


misc : IO TestPool
misc
  = mkPool "misc" "Miscellaneous"

files : IO TestPool
files
  = mkPool "files" "File Handling"

examples : IO TestPool
examples
  = mkPool "examples"
           "Working examples"

covering
main : IO ()
main
  = runner [ !misc
           , !files
           , !examples
           ]

-- [ EOF ]
