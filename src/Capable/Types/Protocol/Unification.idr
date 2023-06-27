|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Capable.Types.Protocol.Unification

import Decidable.Equality
import Data.String

import public Data.Singleton

import Data.List.Elem
import Data.List1
import Data.List.Quantifiers

import Toolkit.Decidable.Do
import public Toolkit.Decidable.Informative
import public Toolkit.Decidable.Equality.Indexed

import Toolkit.Data.List.Quantifiers

import public Toolkit.Data.DList
import Toolkit.Data.DList.All

import public Toolkit.DeBruijn.Renaming


import Capable.Bootstrap
import Capable.Error
import Capable.Types.Role
import Capable.Types.Base

import Capable.Types.Protocol.Local
import Capable.Types.Protocol.Local.Synth
import Capable.Types.Protocol.Selection

%default total

mutual
  namespace Branch
    public export
    data Unify : (this : Branch Local.Local ks rs x)
              -> (that : Branch Synth.Local ks rs y)
                      -> Type
      where
        B : Unify this that
         -> Unify (B l t this)
                  (B l t that)

  namespace Cases

    public export
    data Unify : (this : Local.Local ks rs)
              -> (that : Synth.Branches ks rs lbs)
                      -> Type
      where
        Nil : Unify this Nil
        (::) : Protocol.Unify this that
            -> Cases.Unify this those
            -> Unify this
                     (B l t that::those)

  namespace Branches

    public export
    data Unify : (this : Local.Branches ks rs las)
              -> (that : Synth.Branches ks rs lbs)
                      -> Type
      where
        Nil : Unify Nil Nil
        (::) : Branch.Unify this  that
            -> Branches.Unify these those
            -> Unify (this::these)
                     (that::those)

  namespace Protocol
    public export
    data Unify : (this : Local.Local ks rs)
              -> (that : Synth.Local ks rs)
                      -> Type

      where
        Crash : Unify (Crash IsProj) (Crash IsSyn)
        End : Unify End End
        Call : Unify (Call idx) (Call idx)
        Rec  : Unify this that
            -> Unify (Rec k this) (Rec k that)

        Select : {this : _}
              -> Select (B l tyM this)
                        (F l prfM)
                        (o::os)
                        (p::ps)
              -> Protocol.Unify this that
              -> Unify (ChoiceL SELECT target (Val (UNION (f:::fs))) (UNION (p::ps)) (o::os))
                       (Select         target l tyM prfM that)

        Choice : Unify these those
              -> Unify (ChoiceL BRANCH target ty prfOS these)
                       (Offer          target ty prfOS those)

        Choices : Unify this those
               -> Unify this (Choices those)

-- [ EOF ]
