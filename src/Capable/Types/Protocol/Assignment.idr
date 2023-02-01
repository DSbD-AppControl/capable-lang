|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Capable.Types.Protocol.Assignment

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
import public Toolkit.Data.DList.Elem
import Toolkit.Data.DList.All

import public Toolkit.DeBruijn.Renaming


import Capable.Bootstrap
import Capable.Types.Role
import Capable.Types.Base

import Capable.Types.Protocol
import Capable.Types.Protocol.Projection

%default total

public export
Roles : (rs : List Role) -> (ss : List Role) -> Type
Roles rs
  = DList Role (IsVar rs)


namespace List
  public export
  data Union : (xs,ys,zs : List a) -> Type where
    End : Union Nil ys ys
    Pos : Elem x ys
       -> Union     xs  ys zs
       -> Union (x::xs) ys zs
    Neg : Not (Elem x ys)
       -> Union xs      ys     zs
       -> Union (x::xs) ys (x::zs)

  export
  union : DecEq a
       => (xs,ys : List a)
                -> DPair (List a) (Union xs ys)

  union [] ys
    = (ys ** End)

  union (x :: xs) ys with (union xs ys)
    union (x :: xs) ys | (zs ** prf) with (isElem x ys)
      union (x :: xs) ys | (zs ** prf) | (Yes prfR)
        = (zs ** Pos prfR prf)
      union (x :: xs) ys | (zs ** prf) | (No contra)
        = (x :: zs ** Neg contra prf)

namespace DList
  public export
  data Union : (xs : DList a p ps)
            -> (ys : DList a p ps')
            -> (zs : DList a p ps'')
            -> (prf : Union ps ps' ps'') -> Type
    where
      End : Union Nil ys ys End
      Pos : {xs : DList a p ps}
         -> {ys : DList a p ps'}
         -> Union     xs  ys zs rest
         -> Union (x::xs) ys zs (Pos prf' rest)
      Neg : {xs : DList a p ps}
         -> {ys : DList a p ps'}
         -> Union xs      ys     zs rest
         -> Union (x::xs) ys (x::zs) (Neg prf' rest)


  union' : (xs  : DList a p ps)
        -> (ys  : DList a p ps')
        -> (prf : Union ps ps' ps'')
               -> (zs : DList a p ps'' ** Union xs ys zs prf)
  union' [] ys End
    = (ys ** End)

  union' (elem :: rest) ys (Pos x y) with (union' rest ys y)
    union' (elem :: rest) ys (Pos x y) | (zs ** prf)
      = (zs ** Pos prf)

  union' (elem :: rest) ys (Neg f x) with (union' rest ys x)
    union' (elem :: rest) ys (Neg f x) | (zs ** prf)
      = (elem :: zs ** Neg prf)

  export
  union : DecEq a
       => {ps, ps' : _}
       -> (xs  : DList a p ps)
       -> (ys  : DList a p ps')
              -> (ps'' : List a ** zs : DList a p ps''     **
                  prf : Union ps ps' ps'' ** Union xs ys zs prf)
  union {ps} {ps'} xs ys with (Assignment.List.union ps ps')
    union {ps = ps} {ps' = ps'} xs ys | (zs ** prf) with (union' xs ys prf)
      union {ps = ps} {ps' = ps'} xs ys | (zs ** prf) | (rest ** prf') = (zs ** rest ** prf ** prf')

mutual
  namespace Protocol
    public export
    data HasRoles : (rs : List Role)
                 -> (lp : Local ks rs)
                 -> (os : Roles rs ss)
                       -> Type
      where
        Crash : HasRoles rs lp os
        End   : HasRoles rs lp os
        Call  : HasRoles rs lp os
        Rec   : HasRoles rs lp os
             -> HasRoles rs lp os
        Choice : Branches.HasRoles rs bs os
              -> Union [whom] os os' prf
              -> Protocol.HasRoles rs (Choice kind whom ty bs) os'

  namespace Branch
    public export
    data HasRoles : (rs : List Role)
                 -> (lp : Branch Local ks rs l)
                 -> (os : Roles rs ss)
                       -> Type
      where
        B : Protocol.HasRoles rs        l  os
         ->   Branch.HasRoles rs (B m t l) os

  namespace Branches
    public export
    data HasRoles : (rs : List Role)
                 -> (lp : Local.Branches ks rs lts)
                 -> (os : Roles rs ss)
                       -> Type
      where
        Nil : HasRoles rs Nil Nil

        Add :   Branch.HasRoles rs b os
           -> Branches.HasRoles rs bs os'
           -> Union os os' os'' prf
           -> Branches.HasRoles rs (b::bs) os''


-- [ EOF ]
