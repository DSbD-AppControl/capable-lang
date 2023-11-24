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
import Capable.Pretty

import Capable.Codegen.Rust
import Capable.Options

%default total

showToks : (List (WithBounds Token)) -> List String
showToks = map (\(MkBounded t _ _) => show t)


codegen : Target -> Prog p -> Capable ()
codegen RUST et
  = do putStrLn "```"
       putStrLn "Not Yet Realised" -- (Rust.codegen et)
       putStrLn "```"

getFile : Opts -> Capable String
getFile o
  = maybe (throw $ Generic Options.helpStr)
          pure
          (file o)

export
pipeline : Opts -> Capable ()
pipeline opts
  = do when (help opts)
         $ do putStrLn helpStr
              exitSuccess

       fname <- getFile opts
       let fargs = args opts

       when (justLex opts)
         $ do toks <- lexFile fname
              putStrLn $ unlines (showToks toks)
              exitSuccess

       ast <- fromFile fname
       when (showAST opts)
         $ printLn ast

       putStrLn "# Finished Parsing"

       (tm, st, (_ ** et)) <- check ast
       putStrLn "# Finished Type Checking"

       when (justCheck opts)
         $ do prettyHoles st
              exitSuccess

       when (pprint opts)
         $ do putStrLn "```"
              putStrLn (toString ast)
              putStrLn "```"
              exitSuccess

       when (ppLaTeX opts)
         $ do putStrLn "```"
              putStrLn (toLaTeX ast)
              putStrLn "```"
              exitSuccess

       True <- hasNoHoles st
         | False =>  do prettyHoles st
                        exitSuccess

       case codegen opts of
         Just t => codegen t et
         Nothing
           => do putStrLn "# Executing"
                 putStrLn "```"
                 v <- exec fargs tm
                 putStrLn "```"
                 putStrLn "# Finished"
                 exitSuccess

-- [ EOF ]
