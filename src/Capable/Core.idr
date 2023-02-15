||| The Core Computation Context.
|||
||| Module    : Core.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
||| `TheRug` is defined in the toolkit. Here we establish the synonyms
||| required for Capable.
|||
module Capable.Core

import        System

import        Data.String

import public Toolkit.TheRug
import        Toolkit.System

import public Capable.Bootstrap
import public Capable.Error
import public Capable.Error.Pretty

%default total

public export
%inline
Capable : Type -> Type
Capable = TheRug Capable.Error

namespace Capable

  %inline
  whenErr : (msg : Capable.Error)
                -> IO ()
  whenErr err
    = do putStrLn (show err)
         exitWith (ExitFailure 1)

  %inline
  whenOK : a -> IO ()
  whenOK _ = pure ()

  export
  run : (prog : Capable a)
             -> IO ()
  run = run whenErr whenOK

-- [ EOF ]
