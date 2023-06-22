module Capable.Options

import Data.String

import System

import Toolkit.Options.ArgParse

import Capable.Core

%default total

public export
data Target = RUST

export
Show Target where
  show RUST = "RUST"

export
Eq Target where
  (==) RUST RUST = True

record IOpts where
  constructor O
  justLex   : Bool
  showAST   : Bool
  justCheck : Bool
  pprint    : Bool
  ppLaTeX   : Bool
  launchREPL : Bool
  help       : Bool
  codegen   : Maybe Target
  file     : List String


export
helpStr : String
helpStr
  =   banner
  <+> -- Random space below is for banner alignment.
"""


Usage: capable [options] [input file] [args]

Options:

  --help Show help information.

  --repl launch the REPL

  --check  Only type check
  --latex  type check and pretty print LaTeX
  --pretty type check and pretty print

  --codegen=[target] Generate code for given target language
                     Currently supported target is RUST

  --codegen-rust Generate code for RUST

  --lex Dump the tokens from lexing
  --ast Dump parsed AST
"""



export
Show IOpts where
  show (O l a c po p r f cg q)
    = "O \{show l} \{show a} \{show c} \{show po} \{show p} \{show r} \{show f} \{show cg} \{show q}"

export
Eq IOpts where
  (==) x y
    =  justLex x   == justLex y
    && showAST x == showAST y
    && justCheck x == justCheck y
    && launchREPL x == launchREPL y
    && pprint x == pprint y
    && ppLaTeX x == ppLaTeX y
    && file x      == file y
    && help x == help y
    && codegen x == codegen y

convOpts : Arg -> IOpts -> Maybe IOpts

convOpts (File x) o
  = Just $ { file := (file o) ++ [x]} o

convOpts (KeyValue k v) o
  = case (k,v) of
      ("codegen","rust")
        => Just $ { codegen := Just RUST} o
      _ => Nothing

convOpts (Flag x) o
  = case x of
      "ast"
        => Just $ { showAST := True } o
      "repl"
        => Just $ { launchREPL := True} o
      "lex"
        => Just $ { justLex := True} o
      "lexOnly"
        => Just $ { justLex := True} o
      "check"
        => Just $ { justCheck := True} o

      "checkOnly"
        => Just $ { justCheck := True} o
      "latex"
        => Just $ { ppLaTeX := True} o
      "pretty"
        => Just $ { pprint := True} o
      "help"
        => Just $ { help := True} o

      "codegen-rust"
        => Just $ { codegen := Just RUST} o
      otherwise => Nothing


defOpts : IOpts
defOpts = O False False False False False False False Nothing Nil


namespace Options
  public export
  record Opts where
    constructor O
    justLex   : Bool
    showAST   : Bool
    justCheck : Bool
    pprint    : Bool
    ppLaTeX   : Bool
    launchREPL : Bool
    help       : Bool
    codegen   : Maybe Target
    file     : Maybe String
    args    : List String

populate : IOpts -> Maybe String -> List String -> Opts
populate (O l a c po p r f cg _)
        = O l a c po p r f cg

process : IOpts -> Capable Opts
process o
  = case (file o) of
      (x::xs) => pure (populate o (Just x) xs)
      _       => pure (populate o Nothing  Nil)

export
getOpts : Capable Opts
getOpts
  = process !(parseArgs (Opts . OError)
                         defOpts
                         convOpts)

-- [ EOF ]
