module Capable.REPL.Load

import Toolkit.Data.Location

import Capable.Types
import Capable.Error.Pretty
import Capable.Core

import Capable.Lexer
import Capable.Parser

import Capable.Raw.AST
import Capable.Raw.Progs

import Capable.Check.Progs

import Capable.Terms

import Capable.State

%default total

export
load : State -> String -> Capable State
load st fname
  = tryCatch (do ast <- fromFile fname
                 putStrLn "# Finished Parsing"

                 (_,st,et) <- check ast
                 putStrLn "# Finished Type Checking"

                 pure st
              )
              (\err => do printLn err; pure st)
-- [ EOF ]
