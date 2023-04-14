module Client



import System
import System.File

import Data.String

import Network.Socket

namespace Main
  export
  main : IO ()
  main
    = do Right sock <- socket AF_UNIX Stream 0
           | Left err => putStrLn "Error creating \{show err}"

         res <- connect sock (Hostname "/tmp/capable-test.sock") 0

         if not (res == 0)
          then putStrLn "Error connecting \{show res}"
          else do Right res <- send sock "Echo\n"
                    | Left err => putStrLn "Error sending \{show err}"
                  putStrLn "Sent Echo"

                  Right msg <- recvAll sock
                    | Left err => putStrLn "Error receiving \{show err}"
                  putStrLn "Server says: \{msg}"
