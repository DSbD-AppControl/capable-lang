module Ola.Options

import System
import Toolkit.Options.ArgParse

import Ola.Core

%default total

public export
record Opts where
  constructor O
  justLex   : Bool
  justCheck : Bool
  file      : Maybe String

export
Show Opts where
  show (O l c f)
    = "O \{show l} \{show c} \{show f}"

export
Eq Opts where
  (==) x y
    =  justLex x   == justLex y
    && justCheck x == justCheck y
    && file x      == file y

convOpts : Arg -> Opts -> Maybe Opts

convOpts (File x) o
  = Just $ { file := Just x} o

convOpts (KeyValue k v) o
  = Just o

convOpts (Flag x) o
  = case x of
      "lexOnly"
        => Just $ { justLex := True} o
      "checkOnly"
        => Just $ { justCheck := True} o
      otherwise => Nothing


defOpts : Opts
defOpts = O False False Nothing

export
getOpts : Ola Opts
getOpts
  = parseArgs (Opts . OError)
              defOpts
              convOpts

-- [ EOF ]
