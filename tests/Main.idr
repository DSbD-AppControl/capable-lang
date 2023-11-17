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
  = runner [ !(testsInDir "misc"     "Miscellaneous")
           , !(testsInDir "files"    "File Handling")
           , !(testsInDir "examples" "Working Examples")
           , !(testsInDir "sessions" "Session Types")
           , !(testsInDir "benchmarks" "Programs of interest for benchmarking.")
           , !(testsInDir "classics" "Programs of interest for modelling.")
           , !(testsInDir "paper" "Examples from the paper.")
           ]




-- [ EOF ]
