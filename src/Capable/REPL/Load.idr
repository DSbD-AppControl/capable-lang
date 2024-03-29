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
                 let st : State = { file := Just fname } st
                 putStrLn "# Finished Parsing"

                 (_,st,et) <- check st ast
                 putStrLn "# Finished Type Checking"
                 prettyHoles st
                 pure st
              )
              (\err => do printLn err; pure st)
-- [ EOF ]
