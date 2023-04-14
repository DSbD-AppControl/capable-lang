||| IPC code.
|||
||| We assume that messages are received and sent on lines.
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Capable.Exec.Offers

import Data.Maybe
import Data.Vect
import Data.String
import Data.List.Elem
import Data.List1.Elem
import Data.List.Quantifiers

import System.File

import Toolkit.Data.Vect.Extra
import Toolkit.Data.DList
import Toolkit.Data.DVect

import Capable.Core
import Capable.Terms

import Capable.Values
import Capable.Values.Marshall

import Capable.Exec.Env
import Capable.Exec.Common


%default total

export
getIndex : {o    : Branch  Synth.Local stack_r roles x}
        -> {os   : Synth.Branches stack_r roles xs}
        -> (prf    : Elem (s,a) (x::xs))
        -> (offers : Offers roles rs types globals stack_g stack_l stack_r ty whom (o::os))
        -> DPair (Branch Synth.Local stack_r roles (s,a))
                 (Offer roles rs types globals stack_g stack_l stack_r ty whom)
getIndex Here ((O s body) :: z)
  = (B s _ _ ** O s body)

getIndex (There Here) [O _ _] impossible
getIndex (There (There y)) [O _ _] impossible

getIndex (There w) (y :: (z :: v))
  = getIndex w (z::v)

-- [ EOF ]
