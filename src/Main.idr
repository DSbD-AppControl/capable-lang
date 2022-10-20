module Main

import System
import Ola.Core

import Ola.Pipeline
import Ola.REPL
import Ola.Options


mainRug : Ola ()
mainRug
  = do opts <- getOpts

       if (launchREPL opts)
         then repl
         else pipeline opts

       exitSuccess


main : IO ()
main
  = do Ola.run mainRug

-- [ EOF ]
