||| Parsing capable programs.
|||
||| Copyright : COPYRIGHT
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
{-
newtype : Rule (FileContext, String, DTYPE)
newtype
  = do s <- Toolkit.location
       k <- gives "newtype" UNION
       commit
       r <- Capable.ref
       symbol "="
       s' <- Toolkit.location
       t <- type
       e <- Toolkit.location
       let fs = DVect.fromList [(Branch (FIELD (get r)) (newFC s' e) [t])]

       pure ( newFC s e
            , get r
            , Branch (DTYPE UNION) (newFC s e) fs
            )

-}
data Decl = DeclT FileContext String TYPE
          | DeclN FileContext String DTYPE
          | DeclD FileContext String DTYPE
          | DeclF FileContext String FUNC
          | DeclR FileContext String
          | DeclP FileContext String PROT
          | DeclS FileContext String (AST SESH)

decls : RuleEmpty (List Decl)
decls
    = many (declSesh <|> declNTy <|> declTy <|> declFunc <|> declRole <|> declProt <|> declDTy)
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

    declDTy : Rule Decl
    declDTy
      = do urgh <- datatype
           pure (DeclD (fst urgh)
                       (fst (snd urgh))
                       (snd (snd urgh)))

    declNTy : Rule Decl
    declNTy
      = do s <- Toolkit.location
           keyword "newtype"
           r <- ref
           symbol "("
           s' <- Toolkit.location
           ty <- type
           symbol ")"
           e <- Toolkit.location
           let fs = DVect.fromList [(Branch (FIELD (get r)) (newFC s' e) [ty])]
           pure (DeclN (newFC s e) (get r) (Branch (DTYPE UNION) (newFC s e) fs))

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
       a <- arg
       symbol ")"
       t <- optional (symbol "->" *> keyword "Unit")
       b <- block
       e <- Toolkit.location
       pure (un MAIN (newFC s e)
                     (tri FUN (newFC s e)
                              (Branch ARGS (newFC s e) [a])
                              (null UNIT emptyFC)
                              b
                              )

            )

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

    fold (DeclN fc r ty)
      = bin (DEF r DTYPE) fc ty

    fold (DeclD fc r ty)
      = bin (DEF r DTYPE) fc ty

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
