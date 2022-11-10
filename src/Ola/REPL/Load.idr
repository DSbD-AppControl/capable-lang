module Ola.REPL.Load

import Toolkit.Data.Location

import Ola.Types
import Ola.Error.Pretty
import Ola.Core

import Ola.Lexer
import Ola.Parser

import Ola.Raw.AST
import Ola.Raw.Progs

import Ola.Check.Progs

import Ola.Terms

import Ola.REPL.State

%default total

export
load : State -> String -> Ola State
load st fname
  = tryCatch (do ast <- fromFile fname
                 putStrLn "# Finished Parsing"

                 (_,st) <- check ast
                 putStrLn "# Finished Type Checking"

                 pure st
              )
              (\err => do printLn err; pure st)
-- [ EOF ]
