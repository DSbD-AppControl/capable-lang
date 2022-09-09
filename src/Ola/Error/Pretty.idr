||| Make Error's Pretty.
|||
||| Module    : Pretty.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
module Ola.Error.Pretty

import Data.String
import Data.List1
import System.File
import Toolkit.Data.Location
import Toolkit.System
import Toolkit.Text.Lexer.Run
import Toolkit.Text.Parser.Run

import Text.Lexer
import Ola.Types
import Ola.Error
import Ola.Lexer.Token

-- @TODO Make error messages prettier.

%default total

[olaPF] Show a => Show (ParseFailure a) where
  show err
    = trim $ unlines [show (location err), (error err)]

[olaPE] Show a => Show (ParseError a) where
  show (FError err)
    = trim $ unlines ["File Error: "
                     , show err]
  show (PError err)
    = trim $ unlines (forget (map (show @{olaPF}) err))

  show (LError (MkLexFail l i))
    = trim $ unlines [show l, show i]

Show Ty where
  show CHAR        = "CHAR"
  show STR         = "STR"
  show INT         = "INT"
  show BOOL        = "BOOL"
  show (ARRAY x k) = "(ARRAY \{show x} \{show k})"
  show (PAIR x y)  = "(PAIR \{show x} \{show y})"
  show (UNION x y) = "(UNION \{show x} \{show y})"
  show UNIT        = "UNIT"
  show (REF x)     = "(REF \{show x})"
  show (HANDLE x)  = "(HANDLE \{show x})"
  show (FUNC x y)  = "(\{(assert_total $ show x)} -> \{show y}) "
-- @TODO fix assert_total

Show a => Show (Generic.Error a) where
  show (E v)
    = show v
  show (S loc err)
    = unlines [show loc
              , show err]

Show (Lexing.Error) where
  show (LError _ e) = show e
--    = trim $ unlines [show l, show i]

Show (Parsing.Error) where
  show (PError _ err)
    = show @{olaPE} err


Show (Typing.Error) where
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

  show (UnionExpected ty)
    = "A tagged union was expected but was given:\n\t\{show ty}"

  show (FunctionExpected ty)
    = "A Function was expected but was given:\n\t\{show ty}"

  show (ArrayExpected ty)
    = "Array expected but was given:\n\t\{show ty}"
  show (NotBound ref)
    = "Not a bound identifier:\n\t\{show ref}"
  show (Mismatch given expected)
    = unlines ["Type Mismatch:"
              , "  Given:"
              , "    \{show given}"
              , "  Expected:"
              , "    \{show expected}"
              ]

  show (BoundsError given expected)
    = unlines ["Array out-of-bounds access:"
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

export
Show (Ola.Error) where
  show (Generic err)
    = show err

  show (Lex x)
    = "Lexing Error\n" ++ show x

  show (Parse x)
    = "Parsing Error\n" ++ show x

  show (TyCheck x)
    = "Type Checking Error\n" ++ show x

  show (Exec x)
    = "Runtime Error\n" ++ show x

-- [ EOF ]
