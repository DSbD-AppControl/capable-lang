||| What can go wrong!
|||
||| Module    : Error.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
module Capable.Error

import System.File
import Toolkit.Data.Location
import Toolkit.System
import Toolkit.Text.Lexer.Run
import Toolkit.Text.Parser.Run
import public Toolkit.Options.ArgParse
import Capable.Types
import Capable.Lexer.Token

%default total
%hide type

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
    OOB : Nat -> Nat -> Typing.Error
    PatternsMissing : List Base -> Typing.Error
    RedundantPatterns : List String -> Typing.Error

    RedundantCases : List String -> Typing.Error
    CasesMissing : List (String,Base) -> Typing.Error
    WrongLabel : (x,y : String) -> Typing.Error
    Uncomparable : Typing.Error
    NatExpected : Typing.Error
    PairExpected : Ty.Base -> Typing.Error
    ArrayAppend : Ty.Base -> Ty.Base -> Typing.Error
    ArgsExpected : List Ty.Base -> Typing.Error
    RedundantArgs : Nat -> Typing.Error
    FunctionExpected : Ty.Method -> Typing.Error
    RecordExpected : Ty.Base -> Typing.Error
    UnionExpected : Ty.Base -> Typing.Error
    HandleExpected : Ty.Base -> Typing.Error
    Unknown : Typing.Error
    RefExpected : Ty.Base -> Typing.Error
    NotBound : Ref -> Typing.Error
    AlreadyBound : Ref -> Typing.Error
    ArrayExpected : Ty.Base -> Error

    MismatchRole : Ref -> Ref -> Typing.Error

    MismatchM : (given,expected : Ty.Method)
                               -> Typing.Error

    Mismatch : (given,expected : Ty.Base)
                              -> Typing.Error

namespace Running
  public export
  data Error : Type where
    Panic : String -> Running.Error
    Outside : FileError -> Running.Error
    NotYetImplemented : Running.Error
    OOB : Int -> Nat -> Running.Error

namespace Capable
  public export
  data Error : Type where
    Generic : String -> Capable.Error
    Opts    : Options.Error -> Capable.Error
    Lex     : Lexing.Error -> Capable.Error
    Parse   : Parsing.Error -> Capable.Error
    TyCheck : Generic.Error Typing.Error -> Capable.Error
    Exec    : Running.Error -> Capable.Error


-- [ EOF ]
