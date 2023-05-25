||| Module    : Main.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
||| Borrowed From Idris2 and improved with Test.Unit
module Main

import Data.List

import Test.Golden

%default total

covering
main : IO ()
main
  = runner [ !(mkPool "misc"     "Miscellaneous")
           , !(mkPool "files"    "File Handling")
           , !(mkPool "examples" "Working Examples")
           , !(mkPool "sessions" "Session Types")
           , !(mkPool "benchmarks" "Programs of interest for benchmarking.")
           ]

  where mkPool : (dirName, poolName : String)
                           -> IO TestPool
        mkPool d p
          = testsInDir d (const True)
                       p [] Nothing

-- [ EOF ]
