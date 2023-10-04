module Capable.Types.Protocol.Merge.Concat

import Decidable.Equality
import Data.String

import public Data.Singleton

import Data.List.Elem
import Data.List1
import Data.List.Quantifiers

import Data.Void

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
import Capable.Types.Protocol.Selection
import Capable.Types.Protocol.Merge.Meet

%default total

public export
data Append : (lxs : List (String,Base))
           -> (pxs : DList (String,Base) Marshable lxs)
           -> (bxs : Local.Branches ks rs lxs)

           -> (lys : List (String,Base))
           -> (pys : DList (String,Base) Marshable lys)
           -> (bys : Local.Branches ks rs lys)

           -> (lzs : List (String,Base))
           -> (pzs : DList (String,Base) Marshable lzs)
           -> (bzs : Local.Branches ks rs lzs)

           -> Type
  where
    Empty : Append Nil Nil Nil
                   lys pys bys
                   lys pys bys
    Extend : Append lxs pxs bxs
                    lys pys bys
                    lzs pzs bzs
          -> Append (l::lxs) (p::pxs) (b::bxs)
                        lys      pys      bys
                    (l::lzs) (p::pzs) (b::bzs)

public export
data Result : (lxs : List (String,Base))
           -> (pxs : DList (String,Base) Marshable lxs)
           -> (bxs : Local.Branches ks rs lxs)

           -> (lys : List (String,Base))
           -> (pys : DList (String,Base) Marshable lys)
           -> (bys : Local.Branches ks rs lys)
                  -> Type
  where
    R : {lzs : _}
     -> (pzs : DList (String,Base) Marshable lzs)
     -> (bzs : Local.Branches ks rs lzs)
     -> (prf : Append lxs pxs bxs
                      lys pys bys
                      lzs pzs bzs)
            -> Result lxs pxs bxs
                      lys pys bys

export
append : {lys : _}
      -> (pxs : DList (String,Base) Marshable lxs)
      -> (bxs : Local.Branches ks rs lxs)

      -> (pys : DList (String,Base) Marshable lys)
      -> (bys : Local.Branches ks rs lys)
             -> Result lxs pxs bxs
                       lys pys bys

append [] [] pys bys
  = R pys bys Empty

append (px :: pxs) (bx::bxs) pys bys with (append pxs bxs pys bys)
  append (px :: pxs) (bx::bxs) pys bys | (R pzs bzs prf)
    = R (px :: pzs) (bx :: bzs) (Extend prf)



{-
public export
data Concat : (pw : DList (String,Base) Marshable iws)
           -> (ws : Local.Branches ks rs iws)
           -> (px : DList (String,Base) Marshable ixs)
           -> (xs : Local.Branches ks rs ixs)

           -> (py : DList (String,Base) Marshable iys)
           -> (ys : Local.Branches ks rs iys)
           -> (izs : List (String,Base))
           -> (pz : DList (String,Base) Marshable izs)
           -> (zs : Local.Branches ks rs izs)
                 -> Type
  where
    YS : Concat Nil Nil Nil Nil py ys lzs py ys

    AX : Concat Nil Nil      pxs       xs py ys      lzs      pz      zs
      -> Concat Nil Nil (px::pxs) (x::xs) py ys (lx::lzs) (px::pz) (x::zs)

    AW : Concat      pws      ws  px xs py ys      lzs      pz      zs
      -> Concat (pw::pws) (w::ws) px xs py ys (lw::lzs) (pw::pz) (w::zs)

public export
data Result : (pw : DList (String,Base) Marshable iws)
           -> (ws : Local.Branches ks rs iws)
           -> (px : DList (String,Base) Marshable ixs)
           -> (xs : Local.Branches ks rs ixs)
           -> (py : DList (String,Base) Marshable iys)
           -> (ys : Local.Branches ks rs iys)
                 -> Type
  where
    R : (izs : List (String,Base))
     -> (pz : DList (String,Base) Marshable izs)
     -> (zs : Local.Branches ks rs izs)
     -> (pf : Concat pw ws px xs py ys izs pz zs)
           -> Result pw ws px xs py ys


export
concat : {iws, ixs, iys : _}
      -> (pw : DList (String,Base) Marshable iws)
      -> (ws : Local.Branches ks rs iws)
      -> (px : DList (String,Base) Marshable ixs)
      -> (xs : Local.Branches ks rs ixs)
      -> (py : DList (String,Base) Marshable iys)
      -> (ys : Local.Branches ks rs iys)
            -> Result pw ws px xs py ys


concat [] [] [] [] pys ys
  = R _ pys ys YS

concat [] [] (px :: pxs) (x :: xs) py ys
  = let R _ pzs zs prf = concat Nil Nil pxs xs py ys
    in R _ (px::pzs) (x::zs) (AX prf)

concat (pw :: pws) (w :: ws) px xs py ys
  = let R _ pzs zs prf = concat pws ws px xs py ys
    in R _ (pw::pzs) (w :: zs) (AW prf)

public export
data HowMany : (c : Concat pw ws px xs py ys lzs pz zs)
           -> Type
  where
    Empty : {c : Concat Nil Nil Nil Nil Nil Nil Nil Nil Nil} -> HowMany c
    One   : {ly : (String,Base)}
         -> {lzs : List (String,Base)}
         -> {z  : Branch Local ks rs ly}
         -> {pz  : Marshable ly}
         -> {pzs : DList (String,Base) Marshable lzs}
         -> {zs : Local.Branches ks rs lzs}
         -> {c : Concat pw w px x py y (ly::lzs) (pz::pzs) (z::zs)} -> HowMany c

export
howMany : {lzs : _} -> {pz : DList (String,Base) Marshable lzs}
       -> {zs : Local.Branches ks rs lzs} -> (c : Concat pw ws px xs py ys lzs pz zs) -> HowMany c
howMany YS {lzs = []} {pz = []} {zs = []} = Empty
howMany c {lzs = (l::ls)} {pz = (elem :: rest)} {zs = (z::zs)} = One
-}

-- [ EOF ]
