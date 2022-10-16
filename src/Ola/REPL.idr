module Ola.REPL

import System
import System.File
import System.REPL

import Data.String

import Toolkit.Options.ArgParse

import Ola.Core
import Ola.Error.Pretty

import Ola.Lexer
import Ola.Parser
import Ola.Check.Common
import Ola.Check
import Ola.Check.Roles

import Ola.Terms
import Ola.Terms.Protocols.Projection
import Ola.Exec

import Ola.REPL.Load
import Ola.REPL.State

%default total

data SubCommand
  = Load String  -- A file
  | AskTy String -- A name
  | Help
  | Run (Maybe String)   -- A file
  | Proj String String

data Command = S SubCommand | Quit

parseCmd : String -> Maybe Command
parseCmd str
    = parse' (words str)
  where
    parse' : List String
          -> Maybe Command
    parse' [":load", fname]
      = Just (S $ Load fname)

    parse' [":l", fname]
      = Just (S $ Load fname)

    parse' [":type", thing]
      = Just (S $ AskTy thing)

    parse' [":t", thing]
      = Just (S $ AskTy thing)

    parse' [":project", name, role]
      = Just (S $ Proj name role)

    parse' [":p", name, role]
      = Just (S $ Proj name role)

    parse' [":help"]
      = Just (S Help)

    parse' [":?"]
      = Just (S Help)

    parse' [":exec", fname]
      = Just (S $ Run (Just fname))

    parse' [":exec"]
      = Just (S $ Run Nothing)

    parse' [":quit"]
      = Just Quit

    parse' [":q"]
      = Just Quit

    parse' _ = Nothing

helpStr : String
helpStr
  = """
:l :load <fname>          Load a file.
:t :type <expr>           Ask for the type of a thing.
:p :project <name> <role> Project the
:exec [<fname>]           Run the loaded file, or a new one.

:q :quit                  Exit the REPL
:? :help                  Display this help.
"""

prompt : String
prompt
  = ">"






todo : State -> Ola State
todo st = do putStrLn "Not yet implemented"
             pure st


roleCheck' : {roles : List Ty.Role}
          -> (ctxt  : Context Ty.Role roles)
          -> (syn   : String)
                   -> Maybe (DPair Ty.Role (Role roles))

roleCheck' ctxt str
  = case Lookup.lookup str ctxt of
      No _ _ => Nothing
      Yes prf
        => let (r ** (loc ** prfN)) = deBruijn prf
           in pure (r ** (V loc prfN))

process : State -> SubCommand -> Ola State
process st (Load str)
  = load str

process st (AskTy str)
  = todo st

process st Help
  = do putStrLn helpStr
       pure st

process st (Run mstr)
  = todo st

process st (Proj str str1)
  = do Just (P r p) <- getProtocol st str
         | Nothing => do putStrLn "Not a bound protocol: \{str}"
                         pure st


       case roleCheck' r str1 of
         Nothing => do putStrLn "Not a bound role: \{str1}"
                       pure st

         Just (MkRole ** rs) =>
           case Projection.project rs p of
             No msg _ => do putStrLn "Error"
                            pure st
             Yes (R l _) => do putStrLn (toString l)
                               pure st

onInput : State -> String -> Ola (Maybe State)
onInput st l
  = case parseCmd l of
      Nothing => do putStrLn "Invalid Command"
                    putStrLn helpStr
                    pure (Just st)
      Just Quit
        => do putStrLn "Quitting"
              pure Nothing

      Just (S cmd)
        => do st <- process st cmd
              pure (Just st)

-- TODO Fold into Toolkit
-- ADapted from System.REPL
covering
repl' : (st : State)
          -> Ola ()
repl' st
  = do eof <- embed (fEOF stdin)
       if eof
         then pure ()
         else do putStr "Ola> "
                 embed (fflush stdout)
                 x <- embed getLine
                 Just st <- onInput st x
                     | Nothing => pure ()
                 repl' st

export covering
repl : Ola ()
repl = repl' defaultState

-- [ EOF ]
