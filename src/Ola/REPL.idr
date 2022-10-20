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
import Ola.REPL.State

%default total


todo : State -> Ola State
todo st = do putStrLn "Not yet implemented"
             pure st

reflect : (ctxt  : Context a rs)
       -> (loc   : IsVar rs l)
                -> String
reflect [] (V _ Here) impossible
reflect [] (V _ (There later)) impossible

reflect ((I name x) :: rest) (V 0 prf) = name
reflect (elem :: rest) (V (S k) (There later)) = reflect rest (V k later)

showAcc : Nat -> String
showAcc n
  = if lt n 26
         then singleton (chr (cast (plus 97 n)))
         else (singleton (chr (cast (plus 97 (mod n 26))))) <+> (assert_total $ showAcc  (minus n 26))
mutual
  toStringB : (acc : Nat)
           -> (kctxt : Context Kind ks)
           -> (rctxt : Context Ty.Role rs)
           -> Local.Branch ks rs
           -> String
  toStringB acc kctxt rctxt (B label type c)
    = "\{label}(\{show type}) => \{REPL.toString acc kctxt rctxt c}"

  toStringBS : (acc : Nat)
            -> (kctxt : Context Kind ks)
            -> (rctxt : Context Ty.Role rs)
            -> Local.Branches1 ks rs
            -> String
  toStringBS acc kctxt rctxt xs
      = assert_total $ unwords (intersperse "|" (map (toStringB acc kctxt rctxt) (forget xs)))

  toString : (acc : Nat)
          -> (kctxt : Context Kind ks)
          -> (rctxt : Context Ty.Role rs)
          -> (ltype : Local ks rs)
          -> String
  toString acc kctxt rctxt End
    = "End"
  toString acc kctxt rctxt (Call x)
    = "(Call \{reflect kctxt x})"
  toString acc kctxt rctxt (Rec x)
    = let x' = toString (S acc) (extend kctxt (showAcc acc) R) rctxt x
      in "(Rec \{x'})"
  toString acc kctxt rctxt (Choice BRANCH whom cs)
    = "(Branch \{reflect rctxt whom} \{toStringBS acc kctxt rctxt cs})"
  toString acc kctxt rctxt (Choice SELECT whom cs)
    = "(Select \{reflect rctxt whom} \{toStringBS acc kctxt rctxt cs})"

-- acc kctxt rctxt
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
           case Projection.project rs p of
             No msg _ => do putStrLn "Error"
                            todo st
             Yes (R l _) => do putStrLn (REPL.toString Z Nil r l)
                               pure st

export covering
repl : Ola ()
repl = repl "Ola>"
            commands
            defaultState
            process
            printLn
-- [ EOF ]
