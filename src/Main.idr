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

import Ola.Options

showToks : (List (WithBounds Token)) -> List String
showToks = map (\(MkBounded t _ _) => show t)

mainRug : Ola ()
mainRug
  = do opts <- getOpts

       fname <- embed
                  (Generic "File expected.")
                  (file opts)

       when (justLex opts)
         $ do toks <- lexFile fname
              putStrLn $ unwords (showToks toks)
              exitSuccess

       ast <- fromFile fname
       putStrLn "# Finished Parsing"

       tm <- progCheck ast
       putStrLn "# Finished Type Checking"

       when (justCheck opts)
         $ exitSuccess

       putStrLn "# Executing"
       putStrLn "```"
       v <- exec tm
       putStrLn "```"
       putStrLn "# Finished"
       pure ()


main : IO ()
main
  = do Ola.run mainRug

-- [ EOF ]
