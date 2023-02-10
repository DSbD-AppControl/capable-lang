||| Customised computation environment for Executing programs.
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Capable.Exec.Common

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
import Capable.Env
import Capable.Values
import Capable.Values.Marshall

%default total
%hide type

-- # Rug Adaptations

export
throw : Running.Error -> Capable a
throw = (throw . Exec)

export
panic : (why : String) -> Capable a
panic = (throw . Panic)

export
error : (why : FileError) -> Capable a
error = (throw . Outside)

export
todo : Capable a -- i know...
todo = throw NotYetImplemented


-- [ EOF ]
