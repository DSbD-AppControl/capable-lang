module Main

import System
import Ola.Core

import Ola.Pipeline
import Ola.REPL
import Ola.Options


mainRug : Ola ()
mainRug
  = do opts <- getOpts

       when (launchREPL opts) $ do repl
                                   exitSuccess

       pipeline opts
       exitSuccess


main : IO ()
main
  = do Ola.run mainRug

-- [ EOF ]
