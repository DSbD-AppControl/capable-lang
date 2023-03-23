|||
|||
||| Module    : Parser.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
module Capable.Parser

import Data.List1

import public Capable.Lexer
import Capable.Parser.API

import Capable.Core
import Capable.Types

import Capable.Raw.AST

import Capable.Parser.Roles
import Capable.Parser.Types
import Capable.Parser.Protocols
import Capable.Parser.Exprs
import Capable.Parser.Funcs
import Capable.Parser.Sessions

%default partial

data Decl = DeclT    FileContext String TYPE
          | DeclF    FileContext String FUNC
          | DeclR    FileContext String
          | DeclP    FileContext String PROT
          | DeclS    FileContext String (AST SESH)

decls : RuleEmpty (List Decl)
decls
    = many (declSesh <|> declTy <|> declFunc <|> declRole <|> declProt)
  where
    declProt : Rule Decl
    declProt
      = do s <- Toolkit.location
           keyword "protocol"
           r <- ref
           symbol "="
           r' <- protocol
           e <- Toolkit.location
           pure (DeclP (newFC s e) (get r) r')

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

    declSesh : Rule Decl
    declSesh
      = do s <- Toolkit.location
           fs <- session
           e <- Toolkit.location
           pure (DeclS (newFC s e) (get $ fst fs) (snd fs))

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
      = bin (DEF r SESH) fc s

    fold (DeclP fc r s)
      = bin (DEF r PROT) fc s

    fold (DeclR fc r)
      = bin (DEF r ROLE) fc (null (ROLE r) fc)

    fold (DeclT fc r ty)
      = bin (DEF r TYPE) fc ty

    fold (DeclF fc r f)
      = bin (DEF r FUNC) fc f

namespace Capable

  export
  fromFile : (fname : String)
                   -> Capable PROG
  fromFile fname
    = do ast <- parseFile (\p => Parse (PError fname p))
                Capable.Lexer
                program
                fname
         pure (AST.setSource fname ast)

-- [ EOF ]
