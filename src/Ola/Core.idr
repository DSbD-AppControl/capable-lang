||| The Core Computation Context.
|||
||| Module    : Core.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
||| `TheRug` is defined in the toolkit. Here we establish the synonyms
||| required for Ola.
|||
module Ola.Core

import        System

import        Data.String

import public Toolkit.TheRug
import        Toolkit.System

import public Ola.Error
import        Ola.Error.Pretty

%default total

public export
%inline
Ola : Type -> Type
Ola = TheRug Ola.Error

namespace Ola

  %inline
  whenErr : (msg : Ola.Error)
                -> IO ()
  whenErr err
    = do putStrLn (show err)
         exitWith (ExitFailure 1)

  %inline
  whenOK : a -> IO ()
  whenOK _ = pure ()

  export
  run : (prog : Ola a)
             -> IO ()
  run = run whenErr whenOK

-- [ EOF ]
