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
import public Toolkit.Options.ArgParse
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

namespace Options
  public export
  data Error : Type where
    OError : ArgParseError -> Options.Error

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
    Uncomparable : Typing.Error
    NatExpected : Typing.Error
    PairExpected : Ty.Base -> Typing.Error
    ArrayAppend : Ty.Base -> Ty.Base -> Typing.Error
    ArgsExpected : List Ty.Base -> Typing.Error
    RedundantArgs : Nat -> Typing.Error
    FunctionExpected : Ty.Base -> Typing.Error
    UnionExpected : Ty.Base -> Typing.Error
    HandleExpected : Ty.Base -> Typing.Error
    Unknown : Typing.Error
    RefExpected : Ty.Base -> Typing.Error
    NotBound : Ref -> Typing.Error
    ArrayExpected : Ty.Base -> Error

    MismatchRole : Ref -> Ref -> Typing.Error

    Mismatch : (given,expected : Ty.Base)
                              -> Typing.Error

namespace Running
  public export
  data Error : Type where
    Panic : String -> Running.Error
    Outside : FileError -> Running.Error
    NotYetImplemented : Running.Error
    OOB : Int -> Nat -> Running.Error

namespace Ola
  public export
  data Error : Type where
    Generic : String -> Ola.Error
    Opts    : Options.Error -> Ola.Error
    Lex     : Lexing.Error -> Ola.Error
    Parse   : Parsing.Error -> Ola.Error
    TyCheck : Generic.Error Typing.Error -> Ola.Error
    Exec    : Running.Error -> Ola.Error


-- [ EOF ]
