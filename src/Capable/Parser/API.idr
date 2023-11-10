||| Common functions for parsing.
|||
||| Copyright : COPYRIGHT
||| License   : see LICENSE
|||
module Capable.Parser.API


import public Text.Parser
import public Data.List.Elem
import public System.File.Mode

import Data.Maybe

import public Toolkit.Data.Location
import public Toolkit.Text.Lexer.Run
import public Toolkit.Text.Parser.Support
import public Toolkit.Text.Parser.Location
import public Toolkit.Text.Parser.Run


import Capable.Core

import public Capable.Lexer.Token
import public Capable.Lexer
import public Capable.Raw.AST

import Capable.Parser.API.Borrowed

%default total


namespace Capable
  public export
  Rule : Type -> Type
  Rule = Rule Unit Token

  public export
  RuleEmpty : Type -> Type
  RuleEmpty = RuleEmpty Unit Token

  export
  fromString : (rule : Rule a)
            -> (fname : String)
                     -> Capable a
  fromString rule str
    = parseString (\p => Parse (PError str p))
                  Capable.Lexer rule str

  export
  eoi : RuleEmpty Unit
  eoi = eoi isEOI
    where
      isEOI : Token -> Bool
      isEOI EndInput = True
      isEOI _ = False


  export
  symbol : (str : String)
               -> Rule Unit
  symbol str
    = terminal ("Expected Symbol '" ++ str ++ "'")
               (\x => case x of
                             Symbol s => if s == str then Just MkUnit
                                                     else Nothing
                             _ => Nothing)

  export
  mode : Rule Mode
  mode
    = terminal "Expected mode str"
               (\x => case x of
                        ModeString "r"  => Just Read
                        ModeString "r+" => Just ReadWrite
                        ModeString "w"  => Just WriteTruncate
                        ModeString "w+" => Just ReadWriteTruncate
                        ModeString "a"  => Just Append
                        ModeString "a+" => Just ReadAppend
                        _ => Nothing)


  export
  char : Rule Char
  char = terminal "Expected char literal"
                  (\x => case x of
                           LitChr c => getCharLit c

                           _ => Nothing)

  export
  string : Rule String
  string = terminal "Expected str literal"
                    (\x => case x of
                             LitStr s => Just s
                             _ => Nothing)

  export
  int : Rule Int
  int = terminal "Expected int literal"
               (\x => case x of
                           LitInt i => Just i
                           _ => Nothing)

  export
  keyword : (str : String)
                -> Rule Builtin.Unit
  keyword str
    = terminal ("Expected Keyword '" ++ str ++ "'")
                 (\x => case x of
                             Keyword s => if s == str then Just Builtin.MkUnit
                                                      else Nothing
                             _ => Nothing)

  identifier : Rule String
  identifier
    = terminal "Expected Identifier"
               (\x => case x of
                                  ID str => Just str
                                  _ => Nothing)

  export
  ref : Rule Ref
  ref =
    do s <- Toolkit.location
       n <- identifier
       e <- Toolkit.location
       pure (MkRef (newFC s e) n)


  export
  keywordLoc : (s : String) -> Rule FileContext
  keywordLoc str
    = do s <- Toolkit.location
         keyword str
         e <- Toolkit.location
         pure (newFC s e)


  export
  withLoc : Rule a -> Rule (FileContext, a)
  withLoc r
    = do s <- Toolkit.location
         v <- r
         e <- Toolkit.location
         pure (newFC s e, v)

  export
  gives : (s : String) -> a -> Rule a
  gives str ctor
    = do keyword str
         pure ctor

  export
  givesWithLoc : (s : String) -> (FileContext -> a) -> Rule a
  givesWithLoc str ctor
    = do loc <- withLoc (keyword str)
         pure (ctor (fst loc))

-- [ EOF ]
