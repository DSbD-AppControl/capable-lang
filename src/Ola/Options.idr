module Ola.Options

import System
import Toolkit.Options.ArgParse

import Ola.Core

%default total

public export
record Opts where
  constructor O
  justLex   : Bool
  showAST   : Bool
  justCheck : Bool
  launchREPL : Bool
  file      : Maybe String

export
Show Opts where
  show (O l a c r f)
    = "O \{show l} \{show a} \{show c} \{show r} \{show f}"

export
Eq Opts where
  (==) x y
    =  justLex x   == justLex y
    && showAST x == showAST y
    && justCheck x == justCheck y
    && launchREPL x == launchREPL y
    && file x      == file y

convOpts : Arg -> Opts -> Maybe Opts

convOpts (File x) o
  = Just $ { file := Just x} o

convOpts (KeyValue k v) o
  = Just o

convOpts (Flag x) o
  = case x of
      "ast"
        => Just $ { showAST := True } o
      "repl"
        => Just $ { launchREPL := True} o
      "lexOnly"
        => Just $ { justLex := True} o
      "checkOnly"
        => Just $ { justCheck := True} o
      otherwise => Nothing


defOpts : Opts
defOpts = O False False False False Nothing

export
getOpts : Ola Opts
getOpts
  = parseArgs (Opts . OError)
              defOpts
              convOpts

-- [ EOF ]
