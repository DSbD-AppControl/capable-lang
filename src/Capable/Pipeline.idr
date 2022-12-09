module Capable.Pipeline

import System

import Data.String

import Toolkit.Options.ArgParse

import Capable.Core

import Capable.Lexer
import Capable.Parser
import Capable.Raw.AST
import Capable.Check

import Capable.Terms
import Capable.Exec
import Capable.State

import Capable.Options

%default total

showToks : (List (WithBounds Token)) -> List String
showToks = map (\(MkBounded t _ _) => show t)

export
pipeline : Opts -> Capable ()
pipeline opts
  = do fname <- embed
                  (Generic "File expected.")
                  (file opts)

       when (justLex opts)
         $ do toks <- lexFile fname
              putStrLn $ unlines (showToks toks)
              exitSuccess

       ast <- fromFile fname
       when (showAST opts)
         $ printLn ast

       putStrLn "# Finished Parsing"

       (tm,_) <- check ast
       putStrLn "# Finished Type Checking"

       when (justCheck opts)
         $ exitSuccess

       putStrLn "# Executing"
       putStrLn "```"
       v <- exec tm
       putStrLn "```"
       putStrLn "# Finished"
       pure ()

-- [ EOF ]
