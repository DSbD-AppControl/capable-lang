||| Collecting types together into a single type...
|||
||| Module    : Capable.Types
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Capable.Types

import Decidable.Equality

import Toolkit.Decidable.Informative

import public Capable.Types.Base
import public Capable.Types.Role
import public Capable.Types.Protocol

%default total


||| The types of expressions...
public export
data Ty = B Base
        | L (Local ks rs)


-- [ EOF ]