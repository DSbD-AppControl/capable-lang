||| Views on Roles.
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Capable.Raw.Role

import Data.Vect

import Toolkit.Data.DVect

import Toolkit.Data.Location

import Capable.Types
import Capable.Raw.AST

%default total

public export
data Role : (raw : Raw.AST.ROLE) -> Type where
  R : (s : String)
   -> Role (null (ROLE s) fc)

export
toRole : (raw : Raw.AST.ROLE)
             -> Role raw
toRole (Branch (ROLE str) annot Nil)
  = R str

-- [ EOF ]
