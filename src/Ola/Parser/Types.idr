|||
|||
||| Module    : Types.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
module Ola.Parser.Types

import Data.List1
import Data.Maybe
import Data.Either

import Ola.Core
import Ola.Types

import Ola.Lexer
import Ola.Parser.API

%default total

varType : Rule TYPE
varType
  = do r <- Ola.ref
       pure (null (VARTY (get r)) (span r))

baseType' : Rule TYPE
baseType' =   givesWithLoc "Char"   (null CHAR)
          <|> givesWithLoc "String" (null STR)
          <|> givesWithLoc "Int"    (null INT)
          <|> givesWithLoc "Unit"   (null UNIT)
          <|> givesWithLoc "Bool"   (null BOOL)

mutual

  bi : (k : BIN Shape TYPE TYPE TYPE)
    -> (lb,rb,sep : String)
    -> IsSymbol lb
    => IsSymbol rb
    => IsSymbol sep
    => Rule TYPE
  bi k lb rb sep
    = do s <- Toolkit.location
         symbol lb
         l <- type
         symbol sep
         r <- type
         symbol rb
         e <- Toolkit.location
         pure (bin k (newFC s e) l r)

  array : Rule TYPE
  array
    = do s <- Toolkit.location
         symbol "["
         i <- int
         symbol ";"
         l <- type
         symbol "]"
         e <- Toolkit.location
         pure (un (ARRAY i) (newFC s e) l)

  handle : Rule TYPE
  handle
    = do s <- Toolkit.location
         k <- (keyword "FILE" *> pure FILE <|> keyword "PROC" *> pure PROCESS)
         e <- Toolkit.location
         pure (null (HANDLE k) (newFC s e))

  datatype : Rule TYPE
  datatype
      =  bi PROD  "(" ")" "+"
     <|> bi UNION "<" ">" "|"

  ref : Rule TYPE
  ref
    = do s <- Toolkit.location
         symbol "&"
         l <- type
         e <- Toolkit.location
         pure (un REF (newFC s e) l)


  ||| Parser types aside from Function types.
  export
  type : Rule TYPE

  type
      =   handle
      <|> array
      <|> datatype
      <|> baseType'
      <|> ref
      <|> varType

-- [ EOF ]
