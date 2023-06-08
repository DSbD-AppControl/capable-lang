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

import Capable.Options

%default total

showToks : (List (WithBounds Token)) -> List String
showToks = map (\(MkBounded t _ _) => show t)

process : Opts -> Capable (String, List String)
process o
  = case (file o) of
      (x::xs) => pure (x,xs)
      _       => throw (Generic Options.helpStr)

export
pipeline : Opts -> Capable ()
pipeline opts
  = do when (help opts)
         $ do putStrLn helpStr
              exitSuccess

       (fname,fargs) <- process opts

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


       putStrLn "# Executing"
       putStrLn "```"
       v <- exec fargs tm
       putStrLn "```"
       putStrLn "# Finished"
       pure ()

-- [ EOF ]
