|||
|||
||| Module    : Lexer.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
module Capable.Lexer

import public Data.List.Elem

import public Text.Lexer

import public Toolkit.Text.Lexer.Run

import public Capable.Lexer.Token
import Capable.Core

%default total

namespace Capable
  public export
  Symbols : List String
  Symbols = [ -- special composite symbols
              "->", "==>", ":="

              -- Deliminators
            , "[", "]", "<", ">", "{", "}" , "(", ")"

              -- Plain-old Symbols
            , ","
            , "."
            , ":"
            , "?"
            , "+"
            , "|"
            , "&"
            , "="
            , ";"
            , "!"
            ]


  public export
  Keywords : List String
  Keywords = [ -- Keywords
               "func", "main", "type", "role", "session", "protocol"

             , "as"

             , "local", "var", "let"

             , "loop", "until"

             , "match", "when"

             , "if", "else"

             , "union", "struct"

             -- CTors
             , "true", "false"
             , "unit", "tuple", "tag"

             -- Operations
             , "get", "set", "mut"
             , "and", "not", "or"
             , "lt", "lte", "eq", "gt", "gte"

             , "add", "sub", "mul", "div"

             , "size", "strCons", "slice"

             , "ord", "chr", "string", "toString"

             , "the"
             , "print"

             , "read", "close", "write"
             , "recv", "send"
             , "catch", "crash"

             , "fopen", "popen", "popen2"
             , "index"

             -- Types
             , "Int", "Bool", "String", "Char"
             , "Unit"
             , "FILE"
             , "PROC"

             -- Session
             , "rec", "end"
             , "call"
             , "run", "with"
             ]


identifier : Lexer
identifier = pred startIdent <+> many (pred validIdent)
  where
    startIdent : Char -> Bool
    startIdent '_' = True
    startIdent x = isAlpha x

    validIdent : Char -> Bool
    validIdent '_' = True
    validIdent x = isAlphaNum x

modeStr : Lexer
modeStr
  =   is '#'
  <+> is '('
  <+> oneOf "rwa"
  <+> opt (is '+')
  <+> is ')'

stripQuotes : String -> String
stripQuotes str = substr 1 (length str `minus` 2) str

export
stripM : String -> String
stripM str = substr 2 (length str `minus` 3) str

tokenMap : TokenMap Capable.Token
tokenMap = with List
  [
    (space, WS)

  , (lineComment (exact "--"), LineComment)
  , (blockComment (exact "{-") (exact "-}"), BlockComment)
  , (lineComment (exact "|||"), Documentation)
  , (blockComment (exact "{-|") (exact "|-}"), Documentation)

  , (digits, \x => LitInt (cast {to=Int} x))
  , (modeStr, (ModeString . stripM))
  , (charLit, (LitChr . stripQuotes))
  , (stringLit, (LitStr . stripQuotes))
  ]
  ++
     map (\x => (exact x, Symbol)) Symbols
  ++
  [
    (identifier, (\x => if elem x Keywords then Keyword x else ID x))
  , (any, NotRecognised)
  ]

keep : WithBounds Token -> Bool
keep (MkBounded t _ _) = case t of
    BlockComment _ => False
    LineComment  _ => False
    Documentation _ => False
    WS           _ => False
    _              => True


namespace Capable

  public export
  IsKeyword : String -> Type
  IsKeyword s = Elem s Capable.Keywords

  public export
  IsSymbol : String -> Type
  IsSymbol s = Elem s Capable.Symbols

  export
  Lexer : Lexer Token
  Lexer = MkLexer (Capable.Lexer.tokenMap) keep EndInput

  export
  lexFile : String -> Capable (List (WithBounds Token))
  lexFile fname
    = do toks <- lexFile (\e => Lex (LError fname e))
                         Capable.Lexer
                         fname
         pure toks
-- [ EOF ]
