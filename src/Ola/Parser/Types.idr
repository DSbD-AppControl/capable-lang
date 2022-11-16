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

  tuple : Rule TYPE
  tuple
    = do s <- Toolkit.location
         symbol "("
         f <- type
         symbol ","
         commit
         fs <- sepBy1 (symbol ",") type
         symbol ")"
         e <- Toolkit.location
         pure (Branch PROD (newFC s e) (fromList $ f::head fs::tail fs))

  datatype' : Rule TYPE
  datatype'
    = do s <- Toolkit.location
         k <- (gives "union" UNION <|> gives "struct" STRUCT)
         commit
         symbol "{"
         fs <- sepBy1 (symbol ";") field
         symbol "}"
         e <- Toolkit.location
         pure (Branch (DTYPE k) (newFC s e) (fromList $ head fs :: tail fs))

    where field : Rule FIELD
          field
            = do s <- Toolkit.location
                 l <- ref
                 symbol ":"
                 t <- type
                 e <- Toolkit.location
                 pure (Branch (FIELD (get l)) (newFC s e)[t])

  datatype : Rule TYPE
  datatype
      =  datatype'
     <|> tuple

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
      =assert_total -- I know...
      $ (   handle
      <|> array
      <|> datatype
      <|> baseType'
      <|> ref
      <|> varType)

-- [ EOF ]
