module Capable.REPL

import System
import System.File
import System.REPL

import Data.String

import Toolkit.Options.ArgParse

import Capable.Core
import Capable.Error.Pretty

import Data.Nat
import Data.String
import Capable.Lexer
import Capable.Parser
import Capable.Check.Common
import Capable.Check
import Capable.Check.Roles

import Capable.Types.Protocol.Global.HasRoles

import Capable.Terms
import Capable.Terms.Protocols.Projection
import Capable.Exec

import Capable.REPL.Commands
import Capable.REPL.Load
import Capable.State

import Capable.Options
import Capable.Pretty

%default total


todo : State -> Capable State
todo st = do putStrLn "Not yet implemented"
             pure st

roleCheck' : {roles : List Ty.Role}
          -> (ctxt  : Context Ty.Role roles)
          -> (syn   : String)
                   -> Maybe (DPair Ty.Role (DeBruijn.Role roles))

roleCheck' ctxt str
  = case Lookup.lookup str ctxt of
      No _ _ => Nothing
      Yes prf
        => let (r ** (loc ** prfN)) = deBruijn prf
           in pure (r ** (V loc prfN))

export
process : Opts -> State -> Cmd -> Capable State
process o st Quit
  = do putStrLn "Exiting the REPL"
       exitSuccess

process o st (Load str)
  = load st str

process o st (AskTy str)
  = todo st

process o st Help
  = do putStrLn Commands.helpStr
       pure st

process o st (Run args)
  = maybe (do putStrLn "Need to load a program first."
              pure st)
          (\p => do v <- exec (words args) p
                    printLn v
                    pure st)
          (prog st)

process _ st (Project str str1)
  = do Just (P r g p) <- getProtocol st str
         | Nothing => do putStrLn "Not a bound protocol: \{str}"
                         pure st


       case roleCheck' r str1 of
         Nothing => do putStrLn "Not a bound role: \{str1}"
                       pure st

         Just (_ ** rs) =>
           case Projection.Closed.project rs p of
             No msg _ => do putStrLn "Error projecting on: \{str1}."
                            printLn msg
                            pure st
             Yes (R l _) => do putStrLn (toString r l)
                               pure st
process _ st (Roles str)
  = do Just (P r g p) <- getProtocol st str
         | Nothing => do putStrLn "Not a bound protocol: \{str}"
                         pure st

       let R os prf = Protocol.hasRoles g
       traverse_ (\o => putStrLn $ (reflect r o)) os
       pure st

covering
capableREPL : State
           -> (process : State -> Cmd -> Capable State)
           -> Capable ()
capableREPL st p
  = repl "Capable>"
         commands
         st
         p
         printLn


covering
runREPL : Opts -> State -> Capable ()
runREPL o st
  = do putStrLn banner
       putStrLn "\n  Type :? for help.\n"
       capableREPL st (process o)

export covering
repl : Opts -> Capable ()
repl o
  = maybe (runREPL o defaultState)
          (\fname => runREPL o !(process o defaultState (Load fname)))
          (file o)

-- [ EOF ]
