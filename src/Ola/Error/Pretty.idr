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

Show HandleKind where
  show FILE = "FILE"
  show PROCESS = "PROCESS"

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
  show (FUNC x y)  = "(\{show x} -> \{show y}) "

Show a => Show (Generic.Error a) where
  show (E v)
    = show v
  show (S loc err)
    = unlines [show loc
              , show err]

Show (Parsing.Error) where
  show (PError _ err)
    = show @{olaPE} err


Show (Typing.Error) where
  show (Mismatch given expected)
    = unlines ["Type Mismatch:"
              , "  Given:"
              , "    \{show given}"
              , " Expected:"
              , "    \{show expected}"
              ]

  show (BoundsError given expected)
    = unlines ["Array out-of-bounds access:"
              , "  Given:"
              , "    \{show given}"
              , " Expected:"
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
  show (Parse x)
    = "Parsing Error\n" ++ show x

  show (TyCheck x)
    = "Type Checking Error\n" ++ show x

  show (Exec x)
    = "Runtime Error\n" ++ show x

-- [ EOF ]
