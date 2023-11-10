||| Main entry point.
|||
||| Copyright : COPYRIGHT
||| License   : see LICENSE
|||
module Main

import System
import Capable.Core

import Capable.Pipeline
import Capable.REPL
import Capable.Options


mainRug : Capable ()
mainRug
  = do opts <- getOpts

       if (launchREPL opts)
         then repl opts
         else pipeline opts

       exitSuccess


main : IO ()
main
  = do Capable.run mainRug

-- [ EOF ]
