||| What can go wrong!
|||
||| Copyright : COPYRIGHT
||| License   : see LICENSE
|||
module Capable.Error

import System.File
import Language.JSON
import Toolkit.DeBruijn.Context
import Toolkit.DeBruijn.Context.Item
import Toolkit.Data.Location
import Toolkit.System
import Toolkit.Text.Lexer.Run
import Toolkit.Text.Parser.Run
import Toolkit.Data.DVect
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
     -> (err : Generic.Error type)
            -> Generic.Error type

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

namespace Projection
  public export
  data Error : Type where
    NotAllSame : {ks,rs : _} -> Local.Branches ks rs ls -> Projection.Error
    BranchNotProjectionable : String -> Projection.Error -> Projection.Error
    Skip : Projection.Error -> Projection.Error
    Offer : Projection.Error -> Projection.Error
    Select : Projection.Error -> Projection.Error
    Rec : Projection.Error -> Projection.Error

namespace Merge
  public export
  data Error : Type where
    MeetFailCont : String -> Merge.Error -> Merge.Error
    MeetFail : (Branch (Protocol LOCAL) ks rs lx, Branch (Protocol LOCAL) ks rs ly) -> Merge.Error
    WrongRecVar : Error
    InRec : Merge.Error -> Merge.Error
    UnBalancedOffers : Bool -> Merge.Error
    OffersFail : Merge.Error -> Merge.Error
    RoleMismatch : Merge.Error
    TypeMismatch : Base -> Base -> Merge.Error
    EmptySelect : Merge.Error
    Meeting : Merge.Error -> Merge.Error
    NotMergable : Merge.Error
    EmptyFold : Merge.Error

namespace Subset
  public export
  data Error : Type where
    LabelMismatch : (String, String) -> Subset.Error
    TypeMismatch : (Base, Base) -> Subset.Error
    BranchErr : String -> Subset.Error -> Subset.Error
    NotExists : Subset.Error
    Unbalanced : Subset.Error
    WrongRecVar : Subset.Error
    InRec : Subset.Error -> Subset.Error
    OffersFail : Subset.Error -> Subset.Error
    RoleMismatch : Subset.Error
    SelectError : Subset.Error -> Subset.Error
    NotSubset : Subset.Error

namespace Typing
  public export
  data Error : Type where
    WellFormed : String -> Typing.Error
    NotMarshable : (type : Base)
                -> (prf  : MarshableNot type)
                        -> Typing.Error
    OOB : Nat -> Nat -> Typing.Error
    PatternsMissing : List Base -> Typing.Error
    RedundantPatterns : List String -> Typing.Error

    RedundantCases : List String -> Typing.Error
    CasesMissing : List (String,Base) -> Typing.Error
    WrongLabel : (x,y : String) -> Typing.Error
    Uncomparable : Typing.Error
    NatExpected : Typing.Error
    PairExpected : Ty.Base -> Typing.Error
    VectorAppend : Ty.Base -> Ty.Base -> Typing.Error
    ArgsExpected : List Ty.Base -> Typing.Error
    RedundantArgs : Nat -> Typing.Error

    RolesExpected : List String -> Typing.Error
    RedundantRoles : List String -> Typing.Error

    ProjectionError : Typing.Error
    MergeError : String -> Merge.Error -> Typing.Error
    SubsetError : String -> String -> Subset.Error -> Typing.Error
    LabelMismatch : String -> List String -> Typing.Error
    SessionExpected : Ty.Method -> Typing.Error
    FunctionExpected : Ty.Method -> Typing.Error
    RecordExpected : Ty.Base -> Typing.Error
    UnionExpected : Ty.Base -> Typing.Error
    HandleExpected : Ty.Base -> Typing.Error
    Unknown : Typing.Error
    RefExpected : Ty.Base -> Typing.Error
    NotBound : Ref -> Typing.Error
    AlreadyBound : Ref -> Typing.Error
    VectorExpected : Ty.Base -> Error
    ListExpected : Ty.Base -> Error
    IterableExpected : Ty.Base -> Error

    MismatchRole : Ref -> Ref -> Typing.Error
    MismatchRoleS : String -> String -> Typing.Error

    MismatchM : (given,expected : Ty.Method)
                               -> Typing.Error

    Mismatch : (given,expected : Ty.Base)
                              -> Typing.Error

    IllTypedSession : String -> String -> Typing.Error

    MismatchK : String -> String -> Typing.Error

namespace Marshall

  public export
  data Error : Type where

    NotValidJSON : (str : String) -> Marshall.Error

    Mismatch : (prf  : Marshall.Marshable type)
            -> (raw  : JSON)
                     -> Marshall.Error

    MissingElems : (left : Nat)
                -> (prf  : Marshall.Marshable type)
                        -> Marshall.Error

    RedundantElems : (prf  : Marshall.Marshable type)
                  -> (raw  : JSON)
                          -> Marshall.Error

    MissingUples : (prfs  : DVect Base Marshable n types)
                         -> Marshall.Error

    RedundantUples : (raw : JSON)
                         -> Marshall.Error

    IllnumberedUple : (n : Nat)
                   -> (l : String)
                        -> Marshall.Error

    MissingFields : (prfs  : DList (String, Base) Marshable types)
                          -> Marshall.Error

    RedundantFields : (raw : JSON)
                           -> Marshall.Error

    FieldMismatch : (x,y : String)
                        -> Marshall.Error

    TagNot : (l : String)
               -> Marshall.Error
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
    Marsh   : Marshall.Error -> Capable.Error
    Parse   : Parsing.Error -> Capable.Error
    TyCheck : Generic.Error Typing.Error -> Capable.Error
    Exec    : Running.Error -> Capable.Error


-- [ EOF ]
