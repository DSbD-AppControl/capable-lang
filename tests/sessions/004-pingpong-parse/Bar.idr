module Bar

import System
import System.File

import Data.String

namespace Main
  export
  main : IO ()
  main
    = do str <- getLine
         Right str <- fPutStrLn stdout (trim str) | Left err => printLn err
         exitSuccess
