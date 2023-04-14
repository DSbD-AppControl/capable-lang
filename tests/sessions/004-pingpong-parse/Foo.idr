module Foo

import System
import System.File
import System.File.Process
import System.Directory
import System.Escape

import Data.String

namespace Main

  export
  main : IO ()
  main
    = do Right fh <- popen ("./build/exec/bar") WriteTruncate
               | Left err => printLn err

         putStrLn "IDRIS: Receiving"
         Right str <- fGetLine fh
               | Left err => printLn err

         putStrLn "IDRIS: \{str}"
         putStrLn "IDRIS: Sending"
         Right str <- fPutStr fh "{ \"msg\" : 1 }"
               | Left err => printLn err


         putStrLn "IDRIS: Receiving"
         Right str <- fGetLine fh
               | Left err => printLn err

         pclose fh

         putStrLn "IDRIS: \{str}"
         exitSuccess
