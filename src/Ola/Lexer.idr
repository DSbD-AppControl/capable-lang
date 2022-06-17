|||
|||
||| Module    : Lexer.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
module Ola.Lexer

import public Text.Lexer

import public Toolkit.Text.Lexer.Run

import public Ola.Lexer.Token

%default total

symbols : List String
symbols = ["->", "=>", "=", ":=", "[", "]", ":", "{", "}", ",", "(", ")", "|"
          ]


keywords : List String
keywords = [ "def", "fun", "let", "in", "rec", "main"

           , "this", "that"

           , "match", "as", "with"

           , "if", "then", "else"

           , "empty", "extend"

           , "true", "false"
           , "unit"
           , "apply"

           -- Operations
           , "and", "not", "or", "xor", "lessThan"
           , "add", "sub"
           , "pack", "unpack"
           , "size"
           , "toChar", "toNat", "toString"

           -- Types
           , "Nat", "Bool", "String", "Char", "List", "Pair", "Sum"
           , "Unit"
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
     map (\x => (exact x, Symbol)) symbols
  ++
  [
    (identifier, (\x => if elem x keywords then Keyword x else ID x))
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

  export
  Lexer : Lexer Token
  Lexer = MkLexer (Ola.Lexer.tokenMap) keep EndInput

-- [ EOF ]
