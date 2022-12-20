||| Make Error's Pretty.
|||
||| Module    : Pretty.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
module Capable.Error.Pretty

import Data.String
import Data.List1
import System.File
import Toolkit.Data.Location
import Toolkit.System
import Toolkit.Text.Lexer.Run
import Toolkit.Text.Parser.Run

import Text.Lexer
import Capable.Types
import Capable.Types.Base
import Capable.Error
import Capable.Lexer.Token

-- @TODO Make error messages prettier.

%default total

[capablePF] Show a => Show (ParseFailure a) where
  show err
    = trim $ unlines [show (location err), (error err)]

[capablePE] Show a => Show (ParseError a) where
  show (FError err)
    = trim $ unlines ["File Error: "
                     , show err]
  show (PError err)
    = trim $ unlines (forget (map (show @{capablePF}) err))

  show (LError (MkLexFail l i))
    = trim $ unlines [show l, show i]

Show Ty.Role where
  show MkRole = "Role"


-- @TODO fix assert_total

Show Ty where
  show (B x) = show x
  show (L l) = show "L"

Show a => Show (Generic.Error a) where
  show (E v)
    = show v
  show (S loc err)
    = unlines [show loc
              , show err]

Show (Lexing.Error) where
  show (LError _ e) = show e

Show (Options.Error) where
  show (OError err)
    = show err

Show (Parsing.Error) where
  show (PError _ err)
    = show @{capablePE} err


Show (Typing.Error) where
  show (OOB e g)
    = "Index Out of Bounds: Given \{show g}; Expected: \{show e}."

  show (RedundantCases str)
    = unlines ["Redundant cases:"
              , "  \{show str}"]
  show (CasesMissing str)
    = unlines ["Missing cases:"
              , "  \{show str}"]

  show (WrongLabel x y)
    = unlines ["Label Mismatch during matching:"
              , "  Given:"
              , "    \{x}"
              , "  Expected:"
              , "    \{y}"]
  show Uncomparable
    = "Not a comparable type."
  show (NatExpected)
    = "Array indices are natural numbers."
  show (ArrayAppend h t)
    = unlines ["Type Mismatch when adding to Array:"
              , "  Given:"
              , "    \{show h}"
              , "  Expected:"
              , "    \{show t}"
              ]
  show (ArgsExpected tys)
    = "Arguments expected but none were given:\n\t\{unlines $ map show tys}"
  show (RedundantArgs n)
    = "There are \{show n} to many arguments."
  show Unknown
    = "Not enough information to type term."
  show (PairExpected ty)
    = "A pair was expected but was given:\n\t\{show ty}"
  show (RefExpected ty)
    = "Reference expected but was given:\n\t\{show ty}"
  show (HandleExpected ty)
    = "A Handle was expected but was given:\n\t\{show ty}"

  show (RecordExpected ty)
    = "A record was expected but was given:\n\t\{show ty}"

  show (UnionExpected ty)
    = "A tagged union was expected but was given:\n\t\{show ty}"

  show (FunctionExpected ty)
    = "A Function was expected but was given:\n\t\{show ty}"

  show (ArrayExpected ty)
    = "Array expected but was given:\n\t\{show ty}"
  show (NotBound ref)
    = "Not a bound identifier:\n\t\{show (get ref)}"

  show (AlreadyBound ref)
    = "Already bound:\n\t\{show (get ref)}"

  show (Mismatch given expected)
    = unlines ["Type Mismatch:"
              , "  Given:"
              , "    \{show given}"
              , "  Expected:"
              , "    \{show expected}"
              ]

  show (MismatchRole given expected)
    = unlines ["Roles matched:"
              , "  Given:"
              , "    \{show given}"
              , "  Expected:"
              , "    \{show expected}"
              ]

Show (Running.Error) where
  show (Panic x)
    = "Panic:\n" ++ x

  show (Outside x)
    = "Outside Error:\n" ++ show x

  show (NotYetImplemented)
    = "Not Yet Implemented"

  show (OOB e g)
    = "Index Out of Bounds: Given \{show g}; Expected: \{show e}."

export
Show (Capable.Error) where
  show (Generic err)
    = show err

  show (Opts r)
    = "Option Error\n" ++ show r

  show (Lex x)
    = "Lexing Error\n" ++ show x

  show (Parse x)
    = "Parsing Error\n" ++ show x

  show (TyCheck x)
    = "Type Checking Error\n" ++ show x

  show (Exec x)
    = "Runtime Error\n" ++ show x

-- [ EOF ]
