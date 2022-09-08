|||
|||
||| Module    : Types.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
module Ola.Parser.Types

import Data.List1

import Data.Either

import Ola.Core
import Ola.Types

import Ola.Lexer
import Ola.Parser.API

import Ola.Raw.Types

%default total

varType : Rule Raw.Ty
varType
  = do r <- Ola.ref
       pure (TyVar r)

baseType' : Rule (FileContext, Nullary)
baseType' =   gives "Char"   CHAR
          <|> gives "String" STR
          <|> gives "Int"    INT
          <|> gives "Unit"   UNIT
          <|> gives "Bool"   BOOL

baseType : Rule Raw.Ty
baseType = do res <- baseType'
              pure (TyNull (fst res) (snd res))
mutual

  bi : (k : Types.Binary )
    -> (lb,rb,sep : String)
    -> IsSymbol lb
    => IsSymbol rb
    => IsSymbol sep
    => Rule Raw.Ty
  bi k lb rb sep
    = do s <- Toolkit.location
         symbol lb
         l <- type
         symbol sep
         r <- type
         symbol rb
         e <- Toolkit.location
         pure (TyBi (newFC s e) k l r)

  array : Rule Raw.Ty
  array
    = do s <- Toolkit.location
         symbol "["
         i <- nat
         symbol ";"
         l <- type
         symbol "]"
         e <- Toolkit.location
         pure (TyArray (newFC s e) l i)

  handle : Rule Raw.Ty
  handle
    = do k <- (gives "FILE" FILE <|> gives "PROC" PROCESS)
         pure (TyHandle (fst k) (snd k))

  datatype : Rule Raw.Ty
  datatype
      =  bi PAIR  "(" ")" "+"
     <|> bi UNION "<" ">" "|"

  ref : Rule Raw.Ty
  ref
    = do s <- Toolkit.location
         symbol "&"
         l <- type
         e <- Toolkit.location
         pure (TyRef (newFC s e) l)


  ||| Parser types aside from Function types.
  export
  type : Rule Raw.Ty
  type
      =   handle
      <|> array
      <|> datatype
      <|> baseType
      <|> ref
      <|> varType

-- [ EOF ]
