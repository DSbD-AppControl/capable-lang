module Capable.Types.Protocol.Merge.Diff

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
data Diff : (px : DList (String,Base) Marshable ltx)
         -> (xs : Local.Branches ks rs ltx)
         -> (py : DList (String,Base) Marshable lty)
         -> (ys : Local.Branches ks rs lty)
         -> (pz : DList (String,Base) Marshable ltz)
         -> (zs : Local.Branches ks rs ltz)
               -> Type
  where
    Empty : Diff Nil Nil py ys Nil Nil

    Inc : (prf : SharedLabel ks rs x ys -> Void)
       -> (ltr : Diff      pxs      xs  pys ys      pzs      zs)
              -> Diff (px::pxs) (x::xs) pys ys (px::pzs) (x::zs)

    Skip : (prf : SharedLabel ks rs x ys)
        -> (ltr : Diff      pxs      xs  pys ys pzs zs)
               -> Diff (px::pxs) (x::xs) pys ys pzs zs



public export
data Result : (px : DList (String,Base) Marshable ltx)
           -> (xs : Local.Branches ks rs ltx)
           -> (py : DList (String,Base) Marshable lty)
           -> (ys : Local.Branches ks rs lty)
                 -> Type
  where
    R : {lzs : _}
     -> (pz : DList (String,Base) Marshable lzs)
     -> (zs : Local.Branches ks rs lzs)
     -> (pf : Diff   px xs py ys pz zs)
           -> Result px xs py ys

export
diff : (px : DList (String,Base) Marshable ltx)
    -> (xs : Local.Branches ks rs ltx)
    -> (py : DList (String,Base) Marshable lty)
    -> (ys : Local.Branches ks rs lty)
          -> Result px xs py ys
diff [] [] py ys
  = R [] [] Empty

diff (px :: pxs) (x :: xs) py ys with (sharedLabel x ys)
  diff (px :: pxs) (x :: xs) py ys | (Yes prf) with (diff pxs xs py ys)
    diff (px :: pxs) (x :: xs) py ys | (Yes prf) | (R pzs zs pf)
      = R pzs zs (Skip prf pf)

  diff (px :: pxs) (x :: xs) py ys | (No contra) with (diff pxs xs py ys)
    diff (px :: pxs) (x :: xs) py ys | (No contra) | (R pz zs pf)
      = R (px :: pz) (x :: zs) (Inc contra pf)

-- [ EOF ]
