module Capable.Options

import System
import Toolkit.Options.ArgParse

import Capable.Core

%default total

public export
record Opts where
  constructor O
  justLex   : Bool
  showAST   : Bool
  justCheck : Bool
  pprint    : Bool
  ppLaTeX   : Bool
  launchREPL : Bool
  file      : Maybe String

export
Show Opts where
  show (O l a c po p r f)
    = "O \{show l} \{show a} \{show c} \{show po} \{show p} \{show r} \{show f}"

export
Eq Opts where
  (==) x y
    =  justLex x   == justLex y
    && showAST x == showAST y
    && justCheck x == justCheck y
    && launchREPL x == launchREPL y
    && pprint x == pprint y
    && ppLaTeX x == ppLaTeX y
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
      "latex"
        => Just $ { ppLaTeX := True} o
      "pretty"
        => Just $ { pprint := True} o

      otherwise => Nothing


defOpts : Opts
defOpts = O False False False False False False Nothing

export
getOpts : Capable Opts
getOpts
  = parseArgs (Opts . OError)
              defOpts
              convOpts

-- [ EOF ]
