module Capable.REPL.Commands

import Text.Bounded
import Data.Either
import Data.String
import Data.Maybe

import public Toolkit.Commands

import Capable.Core

%default total

public export
data Cmd = Quit
         | Help
         | Load String
         | Run
         | AskTy String
         | Project String String

export
commands : Commands Cmd
commands
  = setCommands
    [
      newCommand (names ["q", "quit", "exit"])
                 Quit
                 "Exit the REPL."

    , newCommand (names ["?", "h", "help"])
                 Help
                 "Show the list of available commands."

    , newCommand (names ["r", "run"])
                 Run
                 "Show the current list of holes."

    , newCommand (names ["load", "l"])
                 (options [REQ "file"])
                 Load
                 "Load a program."

    , newCommand (names ["type", "t"])
                 (options [REQ "name"])
                 AskTy
                 "Get the type of a globally bound definition."

    , newCommand (names ["project", "p"])
                 (options [REQ "protocol", REQ "role"])
                 Project
                 "Project a global type."
    ]

export
Show OptDesc where
  show (REQ str) = "[\{str}]"
  show (OPT str str1) = "<\{str1}> [DEFAULT \{str}]"

export
Show Commands.Error where
  show ExpectedOption = "Option Expected"
  show (ArgsEmpty cds) = "There are more arguments required.\n\t:\{show $ map (\(MkBounded t l w) => show t) cds}"
  show (ToksExpected xs) = "Missing arguments:\n\t \{show xs}"
  show (WrongName strs) = "The name must be one of:\n\t \{show strs}"
  show IsVoid = "Missing colon and/or argument name."
  show ColonExpected = "Commands begin with a colon."
  show NameExpected = "A command was expected."
  show (ArgsExpected xs) = "The following arguments were expected:\n\t \{show xs}"
  show UnRecognised = "Not a recognised command."
  show (LError x) = "Malformed input."

show : CommandDesc a -> String
show cmd
    = trim $ unlines [unwords ["[\{concat $ intersperse "," (map (":" <+>) $ forget $ name cmd)}]"
                              , maybe "" (unwords . map show . forget) (argsDesc cmd)
                              ]
                     , "\t" <+> maybe "" id (help cmd)
                     ]

export
helpStr : String
helpStr
  = unlines (map show (forget commands))

-- [ EOF ]
