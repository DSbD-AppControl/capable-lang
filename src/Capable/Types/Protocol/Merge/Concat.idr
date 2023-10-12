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
                   Nil Nil Nil
                   Nil Nil Nil

    Last : Append Nil Nil Nil
                   lys pys bys
                   lzs pzs bzs
        -> Append Nil Nil Nil
                   (l::lys) (p::pys) (b::bys)
                   (l::lzs) (p::pzs) (b::bzs)

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

append [] [] [] [] = R [] [] Empty
append [] [] (elem :: rest) (b::bys) with (append [] [] rest bys)
  append [] [] (elem :: rest) (b::bys) | (R pzs bzs prf)
    = R (elem :: pzs) (b :: bzs) (Last prf)

append (px :: pxs) (bx::bxs) pys bys with (append pxs bxs pys bys)
  append (px :: pxs) (bx::bxs) pys bys | (R pzs bzs prf)
    = R (px :: pzs) (bx :: bzs) (Extend prf)

-- [ EOF ]
