module Ola.REPL

import System
import System.File
import System.REPL

import Data.String

import Toolkit.Options.ArgParse

import Ola.Core
import Ola.Error.Pretty

import Data.Nat
import Data.String
import Ola.Lexer
import Ola.Parser
import Ola.Check.Common
import Ola.Check
import Ola.Check.Roles

import Ola.Terms
import Ola.Terms.Protocols.Projection
import Ola.Exec

import Ola.REPL.Commands
import Ola.REPL.Load
import Ola.State

import Ola.Pretty

%default total


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

export
process : State -> Cmd -> Ola State
process st Quit
  = do putStrLn "Exiting the REPL"
       exitSuccess

process st (Load str)
  = load st str

process st (AskTy str)
  = todo st

process st Help
  = do putStrLn helpStr
       pure st

process st Run
  = maybe (do putStrLn "Need to load a program first."
              pure st)
          (\p => do v <- exec p
                    printLn v
                    pure st)
          (prog st)

process st (Project str str1)
  = do Just (P r p) <- getProtocol st str
         | Nothing => do putStrLn "Not a bound protocol: \{str}"
                         pure st


       case roleCheck' r str1 of
         Nothing => do putStrLn "Not a bound role: \{str1}"
                       pure st

         Just (MkRole ** rs) =>
           case Projection.Closed.project rs p of
             No msg _ => do putStrLn "Error projecting on: \{str1}."
                            todo st
             Yes (R l _) => do putStrLn (Pretty.toString r l)
                               pure st

export covering
repl : Ola ()
repl = repl "Ola>"
            commands
            defaultState
            process
            printLn
-- [ EOF ]
