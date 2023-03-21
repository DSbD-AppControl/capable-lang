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

export
map : (f : forall a . e a -> Capable (b a))
   -> (xs : DList ty e ts)
         -> Capable (DList ty b ts)
map f [] = pure []
map f (elem :: rest)
  = pure $ !(f elem) :: !(map f rest)


export
foldr : (forall a . e a -> b -> Capable b)
     -> (x  : b)
     -> (xs : DList ty e ts)
           -> Capable b
foldr f acc [] = pure acc
foldr f acc (elem :: rest)
  = f elem !(foldr f acc rest)

export
foldl : (forall a . b -> e a -> Capable b)
     -> (x  : b)
     -> (xs : DList ty e ts)
           -> Capable b
foldl f x [] = pure x
foldl f x (elem :: rest)
  = foldl f (!(f x elem)) rest


export
traverse : (f  : forall a . e a -> Capable (e a))
        -> (xs : DList ty e ts)
              -> Capable (DList ty e ts)
traverse f []
  = pure []
traverse f (elem :: rest)
  = do x <- f elem
       xs <- traverse f rest
       pure (x::xs)
export
traverse_ : (f  : forall a . e a -> Capable ())
         -> (xs : DList ty e ts)
               -> Capable ()
traverse_ f []
  = pure ()
traverse_ f (elem :: rest)
  = do f elem
       traverse_ f rest

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
