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

import Language.JSON

import Toolkit.Data.Location
import Toolkit.System
import Toolkit.Data.DVect
import Toolkit.Text.Lexer.Run
import Toolkit.Text.Parser.Run

import Toolkit.DeBruijn.Context
import Toolkit.DeBruijn.Context.Item

import Text.PrettyPrint.Prettyprinter

import Text.Lexer
import Capable.Bootstrap
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
  show (MkRole s) = "(Role \{s})"


-- @TODO fix assert_total

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

urg : Context Kind ks
   -> Context Ty.Role rs
   -> Branch Local.Local ks rs laty -> Doc ()
urg ctxtk ctxtr (B label type c)
  = group
  $ align
  $ vcat
  [ pretty label <+> parens (pretty (show type))
  , pretty "." <+> pretty (Open.toString ctxtk
                                          ctxtr
                                  c)
  ]

urgh : {rs, ks : _} -> Local.Branches ks rs ls -> Doc ()
urgh bs
  = choices $ mapToList (urg (ctxtK bs) (ctxtR bs)) bs

  where
    ctxtR : {rs : _} -> (bs : Local.Branches ks rs ls) -> Context Ty.Role rs
    ctxtR {rs} _ = rebuild (\(MkRole r) => r)rs

    ctxtK : {ks : _} ->(bs : Local.Branches ks rs ls) -> Context Kind ks
    ctxtK {ks} _ = rebuild (\(R a) => a) ks

export
Show (Projection.Error) where
  show (NotAllSame bs)
    = "Branches differ \n\t\{show $ urgh bs}"

  show (BranchNotProjectionable str x)
    = unlines ["Error projecting branch \{str}:"
              , "\n\t\{show x}"]

  show (Skip x)
    = "Error merging:\n\t\{show x}"

  show (Offer x)
    = "Error generating Offer:\n\t\{show x}"

  show (Select x)
    = "Error generating Select:\n\t\{show x}"

  show (Rec x)
    = "Error generating Rec:\n\t\{show x}"

Show (Typing.Error) where
  show (WellFormed g)
    = "Protocol is not well-formed:\n\t\{g}"
  show (MismatchK e g)
    = "Recursion variable mismatch:\n\t Expected: \{e}\n\t Given: \{g}"
  show (IllTypedSession p)
    = "Session is ill-typed, expecting an expression of type:\n\t\{p}"
  show (ProjectionError)
    = "Error projecting global typing, Error message yet to be realised..."

  show (OOB e g)
    = "Index Out of Bounds: Given \{show g}; Expected: \{show e}."

  show (RedundantPatterns str)
    = unlines ["Redundant patterns:"
              , "  \{show str}"]
  show (PatternsMissing str)
    = unlines ["Missing patterns:"
              , "  \{show str}"]

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

  show (RolesExpected tys)
    = "Following roles are expected:\n\t\{unlines $ map show tys}"
  show (RedundantRoles n)
    = "The following roles are redundant: \{unlines $ map show n}"


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

  show (SessionExpected ty)
    = "A session was expected but was given:\n\t\{show ty}"

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

  show (LabelMismatch s ss)
    = unlines ["Label Mismatch:"
              , "  Given:"
              , "    \{show s}"
              , "  Expected:"
              , "    \{show ss}"
              ]

  show (MismatchM given expected)
    = unlines ["Type Mismatch:"
              , "  Given:"
              , "    \{show given}"
              , "  Expected:"
              , "    \{show expected}"
              ]

  show (MismatchRoleS given expected)
    = unlines ["Roles matched:"
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
  show (NotMarshable type prf)
    = "Not a Marshable type:\n\tGiven:\{show type}\n\tReason:\{show prf}"

Show (Running.Error) where
  show (Panic x)
    = "Panic:\n" ++ x

  show (Outside x)
    = "Outside Error:\n" ++ show x

  show (NotYetImplemented)
    = "Not Yet Implemented"

  show (OOB e g)
    = "Index Out of Bounds: Given \{show g}; Expected: \{show e}"

Show (Marshall.Error) where

  show (Mismatch prf raw)
    = "Error unmarshalling:\n\tExpected:\{show prf}\n\tGiven:\{show raw}"

  show (RedundantElems prf raw)
    = "More array elements than expected:\n\t\{show raw}"

  show (MissingElems n prf)
    = "More array elements expected:\n\t\{show n} are missing"

  show (MissingUples prf)
    = "Missing elements from a tuple:\n\t\{show $ mapToVect show prf}"

  show (RedundantUples raw)
    = "More uples than expected:\n\t\{show raw}"

  show (IllnumberedUple n l)
    = "Tuple uple was wrongly numbered:\n\tExpected: \{show n}\n\tGiven: \{show l}"

  show (MissingFields prfs)
    = let fs = mapToList (\(F k v) =>  "\{k} : \{show v}") prfs
      in "Fields missing:\n\t\{show fs}"

  show (RedundantFields raw)
    = "Fields missing:\n\t\{show raw}"

  show (FieldMismatch x y)
    = "Labels mismatch:\n\tExpected: \{show x}\n\tGiven: \{show y}"

  show (TagNot l)
    = "Not a valid tag: \{show l}"

  show (NotValidJSON str)
    = "Not a valid JSON document: \{show str}"

export
Show (Capable.Error) where
  show (Generic err)
    = show err

  show (Marsh err)
    = "Marsh Error\n" ++ show err

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
