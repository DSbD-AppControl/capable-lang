module Main

import System

import Ola.Core

import Ola.Parser
import Ola.Check

import Ola.Terms
import Ola.Exec


--import Example

processArgs : List String
           -> IO String
processArgs xs
    = do Just f <- processArgs' xs
           | Nothing => do putStrLn "Invalid args."
                           exitFailure
         pure f
  where
    processArgs' : List String
                -> IO (Maybe String)
    processArgs' (x::y::zs)
      = pure $ Just y

    processArgs' _
      = pure $ Nothing

Show LexError where
  show (MkLexFail location input) = show input

mainRug : String -> Ola ()
mainRug fname
  = do ast <- fromFile fname
       printLn "# Finished Parsing"
--       printLn ast
       tm <- progCheck ast
       printLn "# Finished Type Checking"
       printLn "# Executing"
       printLn "```"
       v <- exec tm
       printLn "```"
       printLn "# Finished"
       pure ()


main : IO ()
main
  = do args <- getArgs
       fname <- processArgs args
       Ola.run (mainRug fname)

-- [ EOF ]
