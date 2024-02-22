||| Parsing types in the surface language.
|||
||| Copyright : COPYRIGHT
||| License   : see LICENSE
|||
module Capable.Parser.Types

import Data.List1
import Data.Maybe
import Data.Either

import Capable.Core
import Capable.Types

import Capable.Lexer
import Capable.Parser.API

%default total


varType : Rule TYPE
varType
  = do r <- Capable.ref
       pure (null (VARTY (get r)) (span r))

baseType : Rule TYPE
baseType =   givesWithLoc "Char"   (null CHAR)
         <|> givesWithLoc "String" (null STR)
         <|> givesWithLoc "Int"    (null INT)
         <|> givesWithLoc "Unit"   (null UNIT)
         <|> givesWithLoc "Bool"   (null BOOL)

mutual

  list : Rule TYPE
  list
    = do s <- Toolkit.location
         symbol "["
         l <- type
         symbol "]"
         e <- Toolkit.location
         pure (un LISTY (newFC s e) l)

  vector : Rule TYPE
  vector
    = do s <- Toolkit.location
         symbol "["
         i <- int
         symbol ";"
         l <- type
         symbol "]"
         e <- Toolkit.location
         pure (un (VECTOR i) (newFC s e) l)

  handle : Rule TYPE
  handle
    = do s <- Toolkit.location
         k <- (keyword "FILE" *> pure FILE <|> keyword "PROC" *> pure PROCESS <|> keyword "PIPE" *> pure PIPE)
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
      $ (   baseType
      <|> handle
      <|> vector
      <|> list
      <|> tuple
      <|> ref
      <|> varType)

export
datatype : Rule (FileContext, String, DTYPE)
datatype
  = do s <- Toolkit.location
       k <- (gives "union" UNION <|> gives "struct" STRUCT)
       commit
       r <- Capable.ref
       symbol "{"
       fs <- sepBy1 (symbol ";") field
       symbol "}"
       e <- Toolkit.location
       let fs = DVect.fromList
              $ head fs :: tail fs

       pure ( newFC s e
            , get r
            , Branch (DTYPE k) (newFC s e) fs
            )

  where field : Rule FIELD
        field
          = do s <- Toolkit.location
               l <- ref
               symbol ":"
               t <- type
               e <- Toolkit.location
               pure (Branch (FIELD (get l)) (newFC s e) [t])

-- [ EOF ]
