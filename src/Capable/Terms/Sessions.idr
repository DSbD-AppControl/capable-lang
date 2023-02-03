||| Expressions for session-typed things.
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
||| Ideally we want to capture communication across multiple communication contexts.
||| The reason being is that _how_ we communicate and _deal_ with errors differs depending on the context in which the communication happens.
|||
||| Principally, and in the first instance, we are aiming handle InterProcess Communication contexts.
||| The implementation of which will reside in the `Exec` module.
|||
||| Should we look to add Network and Process based contexts the shape of communication here will change.
|||
module Capable.Terms.Sessions

import Data.List.Elem

import public Data.Fin

import Data.Vect

import System.File

import public Toolkit.Data.DList
import public Toolkit.Data.DVect
import public Toolkit.Data.Vect.Extra

import Capable.Types.Protocol.Selection

import Capable.Terms.Types
import Capable.Terms.Builtins
import Capable.Terms.Vars
import Capable.Terms.Exprs

%default total

%hide type


mutual

  public export
  data Offer : (roles   : List Ty.Role)
            -> (types   : List Ty.Base)
            -> (globals : List Ty.Session)
            -> (stack_g : List Ty.Method)
            -> (stack_l : List Ty.Base)
            -> (stack_r : List Kind) -- recursion variables
            -> (ret     : Ty.Base)
            -> (whom    : IsVar roles MkRole)
            -> (spec    : Branch Local stack_r roles (s,t))
                      -> Type
    where
      O : (s    : String)
       -> (body : Expr  roles types globals stack_g (t::stack_l) stack_r  whom g return)
               -> Offer roles types globals stack_g     stack_l  stack_r         return whom (B s t g)

  public export
  data Offers : (roles   : List Ty.Role)
             -> (types   : List Ty.Base)
             -> (globals : List Ty.Session)
             -> (stack_g : List Ty.Method)
             -> (stack_l : List Ty.Base)
             -> (stack_r : List Kind) -- recursion variables
             -> (ret     : Ty.Base)
             -> (whom    : IsVar roles MkRole)
             -> (os      : Local.Branches stack_r roles lts)
                        -> Type
    where
      Nil : Offers roles types globals stack_g stack_l stack_r ret whom Nil

      (::) : (o  : Offer  roles types globals stack_g stack_l stack_r ret whom o')
          -> (os : Offers roles types globals stack_g stack_l stack_r ret whom os')
                -> Offers roles types globals stack_g stack_l stack_r ret whom (o'::os')


  public export
  data Expr : (roles   : List Ty.Role)
           -> (types   : List Ty.Base)
           -> (globals : List Ty.Session)
           -> (stack_g : List Ty.Method)
           -> (stack_l : List Ty.Base)
           -> (stack_r : List Kind) -- recursion variables
           -> (whom    : IsVar roles MkRole)
           -> (local   : Local ks roles)
           -> (return  : Ty.Base)
                      -> Type
    where
      Seq : Expr roles types globals stack_g stack_l UNIT
         -> Expr roles types globals stack_g stack_l stack_r whom k type
         -> Expr roles types globals stack_g stack_l stack_r whom k type

      ||| Bind things to the *local* stack!
      Let : {type : Ty.Base}
         -> (ty   : Ty         types                                                  type)
         -> (expr : Expr roles types globals stack_g          stack_l                 type)
         -> (rest : Expr roles types globals stack_g (type :: stack_l) stack_r whom k return)
                 -> Expr roles types globals stack_g          stack_l  stack_r whom k return


      LetRec : Expr roles types globals stack_g stack_l (R::stack_r) whom      body  type
            -> Expr roles types globals stack_g stack_l     stack_r  whom (Rec body) type

      Call : (x : IsVar stack_r R)
               -> Expr roles types globals stack_g stack_l stack_r whom (Call x) type

      Crash : Expr roles types globals stack_g stack_l type
           -> Expr roles types globals stack_g stack_l stack_r whom Crash type

      End : Expr roles types globals stack_g stack_l                  type
         -> Expr roles types globals stack_g stack_l stack_r whom End type

      Read : (from   : IsVar roles MkRole)
          -> (offers : Offers  roles types globals stack_g stack_l stack_r type whom (o::os))
          -> (onErr  : Expr roles types globals stack_g stack_l stack_r whom Crash type)
                    -> Expr roles types globals stack_g stack_l stack_r whom
                               (Choice BRANCH from (Val (UNION (m:::ms))) (o::os))
                               type

      Send : (toWhom  : IsVar   roles MkRole)
          -> (payload : Expr    roles types globals stack_g stack_l mtype)
          -> (prf     : Select (B s mtype cont) (o::os))
          -> (rest    : Expr roles types globals stack_g stack_l stack_r whom cont  type)
          -> (onErr   : Expr roles types globals stack_g stack_l stack_r whom Crash type)
                     -> Expr roles types globals stack_g stack_l stack_r whom
                                (Choice SELECT toWhom (Val (UNION (f:::fs))) (o::os))
                                type



public export
data Session : (roles : List Ty.Role)
            -> (types : List Ty.Base)
            -> (sesh  : List Ty.Session)
            -> (stack : List Ty.Method)
            -> (type  :      Ty.Method)
                     -> Type
  where
    Sesh : {args   : List Ty.Base}
        -> {return : Ty.Base}
        -> (body   : Expr    roles types ss stack args Nil whom l return)
                  -> Session roles types ss stack    (SESH whom l args return)

-- [ EOF ]
