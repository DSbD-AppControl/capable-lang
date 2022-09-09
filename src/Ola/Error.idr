||| What can go wrong!
|||
||| Module    : Error.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
module Ola.Error

import System.File
import Toolkit.Data.Location
import Toolkit.System
import Toolkit.Text.Lexer.Run
import Toolkit.Text.Parser.Run

import Ola.Types
import Ola.Lexer.Token

%default total

namespace Generic -- @TODO Pull out to Toolkit?

  ||| Errors can be located deep in a programme's AST, lets provide a
  ||| trace of where.
  public export
  data Error : (type : Type) -> Type where
    E : (v : type) -> Error type
    S : (loc : FileContext)
     -> (err : Error type)
            -> Error type

namespace Lexing
  public export
  data Error : Type where
    LError : String -> LexFail -> Lexing.Error

namespace Parsing
  public export
  data Error : Type where
     PError : String -> ParseError (Token) -> Parsing.Error

namespace Typing
  public export
  data Error : Type where
    PairExpected : Ty -> Typing.Error
    ArrayAppend : Ty -> Ty -> Typing.Error
    ArgsExpected : List Ty -> Typing.Error
    RedundantArgs : Nat -> Typing.Error
    FunctionExpected : Ty -> Typing.Error
    UnionExpected : Ty -> Typing.Error
    HandleExpected : Ty -> Typing.Error
    Unknown : Typing.Error
    RefExpected : Ty -> Typing.Error
    NotBound : Ref -> Typing.Error
    ArrayExpected : Ty -> Error

    Mismatch : (given,expected : Ty)
                              -> Typing.Error
    BoundsError : (given, expected : Nat)
                                  -> Typing.Error

namespace Running
  public export
  data Error : Type where
    Panic : String -> Running.Error
    Outside : FileError -> Running.Error
    NotYetImplemented : Running.Error

namespace Ola
  public export
  data Error : Type where
    Generic : String -> Ola.Error
    Lex     : Lexing.Error -> Ola.Error
    Parse   : Parsing.Error -> Ola.Error
    TyCheck : Generic.Error Typing.Error -> Ola.Error
    Exec    : Running.Error -> Ola.Error


-- [ EOF ]
