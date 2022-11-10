|||
|||
||| Module    : Parser.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
module Ola.Parser

import Data.List1

import public Ola.Lexer
import Ola.Parser.API

import Ola.Core
import Ola.Types

import Ola.Raw.AST

import Ola.Parser.Roles
import Ola.Parser.Types
import Ola.Parser.Protocols
import Ola.Parser.Exprs
import Ola.Parser.Funcs

%default partial

data Decl = DeclT    FileContext String TYPE
          | DeclF    FileContext String FUNC
          | DeclR    FileContext String
          | DeclS    FileContext String PROT

decls : RuleEmpty (List Decl)
decls
    = many (declTy <|> declFunc <|> declRole <|> declSesh)
  where
    declSesh : Rule Decl
    declSesh
      = do s <- Toolkit.location
           keyword "protocol"
           r <- ref
           symbol "="
           r' <- protocol
           e <- Toolkit.location
           pure (DeclS (newFC s e) (get r) r')

    declRole : Rule Decl
    declRole
      = do s <- Toolkit.location
           keyword "role"
           r <- ref
           e <- Toolkit.location
           pure (DeclR (newFC s e) (get r))

    declTy : Rule Decl
    declTy
      = do s <- Toolkit.location
           keyword "type"
           r <- ref
           symbol "="
           ty <- type
           e <- Toolkit.location
           pure (DeclT (newFC s e) (get r) ty)

    declFunc : Rule Decl
    declFunc
      = do s <- Toolkit.location
           fs <- func
           e <- Toolkit.location
           pure (DeclF (newFC s e) (get $ fst fs) (snd fs))

main : Rule PROG
main
  = do s <- Toolkit.location
       keyword "main"
       symbol "("
       symbol ")"
       b <- block
       e <- Toolkit.location
       pure (un MAIN (newFC s e)
                     $ (tri FUN (newFC s e)
                                (Branch ARGS emptyFC Nil)
                                (null UNIT emptyFC)
                                b
                                 ))

export
program : Rule PROG
program
    = do ds <- decls
         m <- main
         eoi
         pure (foldr fold m ds)
  where
    fold : Decl -> PROG -> PROG
    fold (DeclS fc r s)
      = bin (DEF r PROT) fc s

    fold (DeclR fc r)
      = bin (DEF r ROLE) fc (null (ROLE r) fc)

    fold (DeclT fc r ty)
      = bin (DEF r TYPE) fc ty

    fold (DeclF fc r f)
      = bin (DEF r FUNC) fc f

namespace Ola

  export
  fromFile : (fname : String)
                   -> Ola PROG
  fromFile fname
    = do ast <- parseFile (\p => Parse (PError fname p))
                Ola.Lexer
                program
                fname
         pure (AST.setSource fname ast)

-- [ EOF ]
