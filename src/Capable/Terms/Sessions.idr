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

import Capable.Terms.Types
import Capable.Terms.Builtins
import Capable.Terms.Vars
import Capable.Terms.Exprs

import public Capable.Types.Protocol.Projection
import public Capable.Types.Protocol.Subset
import public Capable.Types.Protocol.Merge


%default total

%hide type


mutual
  namespace Cases
    public export
    data Case : (roles   : List Ty.Role)
             -> (rs      : List Ty.Role)
             -> (types   : List Ty.Base)
             -> (globals : List Ty.Session)
             -> (stack_g : List Ty.Method)
             -> (stack_l : List Ty.Base)
             -> (stack_r : List Kind) -- recursion variables
             -> (ret     : Ty.Base)
             -> (whom    : Role roles r)
             -> (ltc     : (String,Base))
             -> (not_b   : Branch Local stack_r roles ltc)
                        -> Type
      where
        C : (s    : String)
         -> (body : Expr roles rs types globals stack_g (t::stack_l) stack_r whom g return)
                 -> Case roles rs types globals stack_g stack_l stack_r return whom (s,t) (B s t g)

    public export
    data Cases : (roles   : List Ty.Role)
              -> (rs      : List Ty.Role)
              -> (types   : List Ty.Base)
              -> (globals : List Ty.Session)
              -> (stack_g : List Ty.Method)
              -> (stack_l : List Ty.Base)
              -> (stack_r : List Kind) -- recursion variables
              -> (ret     : Ty.Base)
              -> (whom    : Role roles r)
              -> (ltcs    : List (String,Base))
              -> (gs      : Local.Branches stack_r roles ltcs)
                         -> Type
      where
        Nil : Cases roles rs types globals sg sl sr ret whom Nil Nil
        (::) : {c : _}
            -> Case  roles rs types globals sg sl sr ret whom ltc c
            -> Cases roles rs types globals sg sl sr ret whom ltcs cs
            -> Cases roles rs types globals sg sl sr ret whom (ltc::ltcs) (c::cs)

  namespace Offers
    public export
    data Offer : (roles   : List Ty.Role)
              -> (rs      : List Ty.Role)
              -> (types   : List Ty.Base)
              -> (globals : List Ty.Session)
              -> (stack_g : List Ty.Method)
              -> (stack_l : List Ty.Base)
              -> (stack_r : List Kind) -- recursion variables
              -> (ret     : Ty.Base)
              -> (whom    : Role roles r)
              -> (spec    : Branch Local stack_r roles (s,t))
                        -> Type
      where
        O : (s    : String)
         -> (body : Expr  roles rs  types globals stack_g (t::stack_l) stack_r  whom g return)
                 -> Offer roles rs  types globals stack_g     stack_l  stack_r         return whom (B s t g)

    public export
    data Offers : (roles   : List Ty.Role)
               -> (rs      : List Ty.Role)
               -> (types   : List Ty.Base)
               -> (globals : List Ty.Session)
               -> (stack_g : List Ty.Method)
               -> (stack_l : List Ty.Base)
               -> (stack_r : List Kind) -- recursion variables
               -> (ret     : Ty.Base)
               -> (whom    : Role roles r)
               -> (os      : Local.Branches stack_r roles lts)
                          -> Type
      where
        Nil : Offers roles rs types globals stack_g stack_l stack_r ret whom Nil

        (::) : (o  : Offer  roles rs types globals stack_g stack_l stack_r ret whom o')
            -> (os : Offers roles rs types globals stack_g stack_l stack_r ret whom os')
                  -> Offers roles rs types globals stack_g stack_l stack_r ret whom (o'::os')


  public export
  data Expr : (roles   : List Ty.Role)
           -> (rs      : List Ty.Role)
           -> (types   : List Ty.Base)
           -> (globals : List Ty.Session)
           -> (stack_g : List Ty.Method)
           -> (stack_l : List Ty.Base)
           -> (stack_r : List Kind) -- recursion variables
           -> (whom    : Role roles r)
           -> (local   : Local stack_r roles)
           -> (return  : Ty.Base)
                      -> Type
    where
      Hole : String
          -> Expr roles rs types globals stack_g stack_l stack_r whom k type

      Seq : Expr       rs types globals stack_g stack_l UNIT
         -> Expr roles rs types globals stack_g stack_l stack_r whom k type
         -> Expr roles rs types globals stack_g stack_l stack_r whom k type

      ||| Bind things to the *local* stack!
      Let : {type : Ty.Base}
         -> (ty   : Ty            types                                                  type)
         -> (expr : Expr       rs types globals stack_g          stack_l                 type)
         -> (rest : Expr roles rs types globals stack_g (type :: stack_l) stack_r whom k return)
                 -> Expr roles rs types globals stack_g          stack_l  stack_r whom k return

      Split : {ss : _}
           -> (expr : Expr       rs types globals stack_g                     stack_l  (TUPLE ss))
           -> (rest : Expr roles rs types globals stack_g (Extra.toList ss ++ stack_l) stack_r whom k return)
                   -> Expr roles rs types globals stack_g                     stack_l  stack_r whom k return

      LetRec : {e,stack_r,body : _}
            -> Expr roles rs types globals stack_g stack_l (e::stack_r) whom        body  type
            -> Expr roles rs types globals stack_g stack_l     stack_r  whom (Rec e body) type

      Cond : {l,r,t : _}
          -> (cond : Expr       rs types globals stack_g stack_l                BOOL)
          -> (tt   : Expr roles rs types globals stack_g stack_l stack_r whom l type)
          -> (ff   : Expr roles rs types globals stack_g stack_l stack_r whom r type)
          -> (prf  : Merge l r t)
                  -> Expr roles rs types globals stack_g stack_l stack_r whom t type

      Match : {l : _}
           -> {a      : (String, Base)}
           -> {as     : List (String, Base)}
           -> {c      : Branch Local stack_r roles a}
           -> {cs     : Local.Branches stack_r roles as}
           -> (expr : Expr rs types globals stack_g stack_l (UNION (a:::as)))
           -> (cases : Cases roles rs types globals stack_g stack_l stack_r type whom (a::as) (c::cs))
           -> (prf    : Many.Merge (c::cs) l)
                    -> Expr roles rs types globals stack_g stack_l stack_r whom l type

      Call : {stack_r,v : _}
          -> (x : RecVar stack_r v)
               -> Expr roles rs types globals stack_g stack_l stack_r whom (Call x) type

      Crash : Expr       rs types globals stack_g stack_l type
           -> Expr roles rs types globals stack_g stack_l stack_r whom (Crash) type

      End : Expr       rs types globals stack_g stack_l                  type
         -> Expr roles rs types globals stack_g stack_l stack_r whom End type

      Read : {m,ms   : _}
          -> (from   : Role roles f)
          -> {o      : Branch Local stack_r roles m}
          -> {os     : Local.Branches stack_r roles ms}
          -> (prf    : Marshable (UNION (m:::ms)))
          -> (offers : Offers roles rs types globals stack_g stack_l stack_r type whom (o::os))
          -> (onErr  : Expr   roles rs types globals stack_g stack_l stack_r whom (Crash) type)
                    -> Expr   roles rs types globals stack_g stack_l stack_r whom
                              (ChoiceL BRANCH from (Val (UNION (m:::ms)))
                                                   prf
                                                   (o::os))
                               type

      Send : {mtype   : _}
          -> (toWhom  : Role roles s)
          -> (label   : String)
          -> (payload : Expr    rs types globals stack_g stack_l mtype)
          -> (mprf    : Marshable mtype)
          -> (rest    : Expr roles rs types globals stack_g stack_l stack_r whom cont  type)
          -> (onErr   : Expr roles rs types globals stack_g stack_l stack_r whom (Crash) type)
                     -> Expr roles rs types globals stack_g stack_l stack_r whom
                                (ChoiceL SELECT toWhom (Val (UNION ((label,mtype):::Nil)))
                                                       (UNION [F label mprf])
                                                       ([B label mtype cont]))

                                type



public export
data Session : (rs    : List Ty.Role)
            -> (types : List Ty.Base)
            -> (sesh  : List Ty.Session)
            -> (stack : List Ty.Method)
            -> (type  :      Ty.Method)
                     -> Type
  where
    Sesh : {args   : List Ty.Base}
        -> {return : Ty.Base}
        -> {local_synth : _}
        -> (idx  : IsVar ss (S ctzt global))
        -> (prfProj  : Protocol.Project Nil roles whom global local_proj)
        -> (prfSub   : Subset local_synth local_proj)
        -> (body   : Expr    roles rs types ss stack args Nil whom local_synth return)
                  -> Session rs types ss stack    (SESH ctzt whom local_proj args return)

-- [ EOF ]
