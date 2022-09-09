module Main

import System

import Data.String

import Toolkit.Options.ArgParse

import Ola.Core

import Ola.Lexer
import Ola.Parser
import Ola.Check

import Ola.Terms
import Ola.Exec

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

showToks : (List (WithBounds Token)) -> List String
showToks = map (\(MkBounded t _ _) => show t)

mainRug : String -> Ola ()
mainRug fname
  = do --toks <- lexFile fname
       --putStrLn $ unwords (showToks toks)
       ast <- fromFile fname
       putStrLn "# Finished Parsing"
--       putStrLn ast
       tm <- progCheck ast
       putStrLn "# Finished Type Checking"
       putStrLn "# Executing"
       putStrLn "```"
       v <- exec tm
       putStrLn "```"
       putStrLn "# Finished"
       pure ()


main : IO ()
main
  = do args <- getArgs
       fname <- processArgs args
       Ola.run (mainRug fname)

-- [ EOF ]
