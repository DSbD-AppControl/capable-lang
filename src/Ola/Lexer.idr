|||
|||
||| Module    : Lexer.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
module Ola.Lexer

import public Data.List.Elem

import public Text.Lexer

import public Toolkit.Text.Lexer.Run

import public Ola.Lexer.Token

%default total

namespace Ola
  public export
  Symbols : List String
  Symbols = [ -- special composite symbols
              "->", ":="

              -- Deliminators
            , "[", "]", "<", ">", "{", "}" , "(", ")"

              -- Plain-old Symbols
            , ","
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
  Keywords = [ "func", "main", "type", "local", "var"

             , "first", "second", "fetch", "alloc", "read", "close"
             , "fopen", "popen", "print", "return", "while"
             , "index", "cond"
             , "match", "when", "split", "as"

             , "write"

             , "call"
             , "if", "else"

             -- CTors
             , "true", "false"
             , "unit", "pair", "left", "right"

             -- Operations
             , "and", "not", "or", "xor", "lessThan"
             , "add", "sub"
             , "pack", "unpack"
             , "size"
             , "toChar", "toNat", "toString"
             , "the"

             -- Types
             , "Int", "Bool", "String", "Char"
             , "Unit", "FILE", "PROC"
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

charLit : Lexer
charLit = is '\'' <+> alphaNum <+> is '\''

stripQuotes : String -> String
stripQuotes str = substr 1 (length str `minus` 2) str

tokenMap : TokenMap Ola.Token
tokenMap = with List
  [
    (space, WS)

  , (lineComment (exact "--"), LineComment)
  , (blockComment (exact "{-") (exact "-}"), BlockComment)
  , (lineComment (exact "|||"), Documentation)
  , (blockComment (exact "{-|") (exact "|-}"), Documentation)

  , (digits, \x => LitNat (integerToNat $ cast {to=Integer} x))
  , (stringLit, (LitStr . stripQuotes))
  , (Ola.Lexer.charLit, (LitChr . stripQuotes))
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


namespace Ola

  public export
  IsKeyword : String -> Type
  IsKeyword s = Elem s Ola.Keywords

  public export
  IsSymbol : String -> Type
  IsSymbol s = Elem s Ola.Symbols

  export
  Lexer : Lexer Token
  Lexer = MkLexer (Ola.Lexer.tokenMap) keep EndInput

-- [ EOF ]
