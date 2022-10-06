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

import Ola.Raw.Roles
import Ola.Raw.Types
import Ola.Raw.Protocols
import Ola.Raw.Exprs
import Ola.Raw.Stmts
import Ola.Raw.Funcs
import Ola.Raw.Progs

import Ola.Parser.Roles
import Ola.Parser.Types
import Ola.Parser.Protocols
import Ola.Parser.Exprs
import Ola.Parser.Stmts
import Ola.Parser.Funcs

%default partial

data Decl = DeclT    FileContext Ref Raw.Ty
          | DeclF    FileContext Ref Raw.Func
          | DeclRsyn FileContext Ref Raw.Role
          | DeclR    FileContext Ref
          | DeclS    FileContext Ref Raw.Protocol

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
           pure (DeclS (newFC s e) r r')

    declRole : Rule Decl
    declRole
      = do s <- Toolkit.location
           keyword "role"
           r <- ref
           r' <- optional (symbol "=" *> role)
           e <- Toolkit.location
           case r' of
             Nothing
               => pure (DeclR (newFC s e) r)
             Just r'
               => pure (DeclRsyn (newFC s e) r r')

    declTy : Rule Decl
    declTy
      = do s <- Toolkit.location
           keyword "type"
           r <- ref
           symbol "="
           ty <- type
           e <- Toolkit.location
           pure (DeclT (newFC s e) r ty)

    declFunc : Rule Decl
    declFunc
      = do s <- Toolkit.location
           fs <- func
           e <- Toolkit.location
           pure (DeclF (newFC s e) (fst fs) (snd fs))

main : Rule Prog
main
  = do s <- Toolkit.location
       keyword "main"
       symbol "("
       symbol ")"
       symbol "{"
       b <- body
       symbol "}"
       e <- Toolkit.location
       pure (Null (newFC s e)
                  (MAIN (Null (newFC s e)
                              $ FUNC Nil
                                     (TyNull emptyFC UNIT)
                                     (fst b)
                                     (snd b))))

export
program : Rule Prog
program
    = do ds <- decls
         m <- main
         eoi
         pure (foldr fold m ds)
  where
    fold : Decl -> Raw.Prog -> Raw.Prog
    fold (DeclS fc r s)
      = Un fc (DEFSESH r s)

    fold (DeclRsyn fc r ro)
      = Un fc (DEFROLESYN r ro)

    fold (DeclR fc r)
      = Un fc (DEFROLE r)

    fold (DeclT fc r ty)
      = Un fc (DEFTYPE r ty)

    fold (DeclF fc r f)
      = Un fc (DEFFUNC r f)

namespace Ola

  export
  fromFile : (fname : String)
                   -> Ola Prog
  fromFile fname
    = do ast <- parseFile (\p => Parse (PError fname p))
                Ola.Lexer
                program
                fname
         pure (setSource fname ast)
           -- @TODO write functers & show for kinds

-- [ EOF ]
