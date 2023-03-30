|||
|||
||| Module    : Token.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
module Capable.Lexer.Token

%default total


public export
data Identifier = MkIdentifier String

export
Eq Identifier where
  (==) (MkIdentifier x) (MkIdentifier y) = x == y

namespace Capable
  public export
  data Token = ID String
              | Keyword String
              | LineComment String
              | BlockComment String
              | Documentation String

              | ModeString String
              | LitInt Int
              | LitStr String
              | LitChr String

              | Symbol String
              | WS String
              | NotRecognised String
              | EndInput

showToken : Show a => String -> a -> String
showToken n a = "(" <+> n <+> " " <+> show a <+> ")"

export
Show Token where
  show (ID id)             = showToken "ID" id
  show (Keyword str)       = showToken "Keyword" str
  show (LineComment str)   = showToken "LineComment" str

  show (BlockComment str)  = showToken "BlockComment" str
  show (Documentation str) = showToken "Documentation" str

  show (ModeString str)    = showToken "ModeString" str
  show (LitInt n) = showToken "Int" n
  show (LitStr s) = "(Str \{s})"
  show (LitChr s) = "(Chr \{s})"

  show (Symbol s) = showToken "Symbol" s
  show (WS ws) = "WS"
  show (NotRecognised s) = showToken "Urgh" s
  show EndInput          = "EndInput"

export
Eq Token where
  (==) (ID x) (ID y) = x == y

  (==) (LineComment x) (LineComment y) = x == y
  (==) (BlockComment x) (BlockComment y) = x == y
  (==) (Keyword x) (Keyword y) = x == y

  (==) (ModeString x) (ModeString y) = x == y
  (==) (LitInt x) (LitInt y) = x == y
  (==) (LitStr x) (LitStr y) = x == y
  (==) (LitChr x) (LitChr y) = x == y

  (==) (Symbol x) (Symbol y) = x == y

  (==) (WS x) (WS y) = x == y
  (==) (NotRecognised x) (NotRecognised y) = x == y
  (==) EndInput EndInput = True
  (==) _ _ = False


-- [ EOF ]
