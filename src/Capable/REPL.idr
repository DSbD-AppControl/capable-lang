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
process : State -> Cmd -> Capable State
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
process st (Roles str)
  = do Just (P r g p) <- getProtocol st str
         | Nothing => do putStrLn "Not a bound protocol: \{str}"
                         pure st

       let R os prf = Protocol.hasRoles g
       traverse_ (\o => putStrLn $ (reflect r o)) os
       pure st



export covering
repl : Capable ()
repl = repl "Capable>"
            commands
            defaultState
            process
            printLn
-- [ EOF ]
