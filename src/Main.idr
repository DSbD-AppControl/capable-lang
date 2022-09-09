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

record Opts where
  constructor O
  justLex   : Bool
  justCheck : Bool
  file      : Maybe String

Show Opts where
  show (O l c f)
    = "O \{show l} \{show c} \{show f}"

Eq Opts where
  (==) x y
    =  justLex x   == justLex y
    && justCheck x == justCheck y
    && file x      == file y

convOpts : Arg -> Opts -> Maybe Opts

convOpts (File x) o
  = Just $ { file := Just x} o

convOpts (KeyValue k v) o
  = Just o

convOpts (Flag x) o
  = case x of
      "lexOnly"
        => Just $ { justLex := True} o
      "checkOnly"
        => Just $ { justCheck := True} o
      otherwise => Nothing

defOpts : Opts
defOpts = O False False Nothing


showToks : (List (WithBounds Token)) -> List String
showToks = map (\(MkBounded t _ _) => show t)

mainRug : Ola ()
mainRug
  = do opts <- parseArgs
                 (Opts . OError)
                 defOpts
                 convOpts

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
