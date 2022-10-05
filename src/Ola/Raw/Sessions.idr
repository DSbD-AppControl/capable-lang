||| AST for Global MPST.
|||
||| Module    : Types.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
||| Let's be smart about the shape of the AST for types.
|||
||| We reduce the *raw* AST to a single tree in which the node values
||| represent extra information about the children.
module Ola.Raw.Sessions

import Data.List1
import Toolkit.Data.Location

import Ola.Types.Session

import Ola.Raw.Roles
import Ola.Raw.Types

%default total

public export
data Nullary = END | CALL Ref

Show Sessions.Nullary where
  show END = "END"
  show (CALL r) = "(CALL \{show r})"

setSourceNull : String -> Sessions.Nullary -> Sessions.Nullary
setSourceNull str END = END
setSourceNull str (CALL r) = CALL (setSource str r)

public export
data Unary = REC Ref

Show Unary where
  show (REC r) = "(REC \{show r})"

public export
data N1Ary = CHOICE Role Role

Show N1Ary where
  show (CHOICE a b)  = "(CHOICE \{show a} \{show b})"

setSourceN : String -> N1Ary -> N1Ary
setSourceN str (CHOICE a b) = CHOICE (setSource str a) (setSource str b)

namespace Raw
  public export
  data Session = Null FileContext Sessions.Nullary
               | Un   FileContext Unary Raw.Session
               | N1   FileContext N1Ary (List1 (String, Raw.Ty, Session))

mutual
  setSources : String -> List (String, Raw.Ty, Session) -> List (String, Raw.Ty, Session)
  setSources str [] = []
  setSources str ((x, y,z) :: xs)
    = (x, setSource str y, setSource str z) :: setSources str xs

  setSources1 : String -> List1 (String, Raw.Ty, Session) -> List1 (String, Raw.Ty, Session)
  setSources1 str ((x,y,z) ::: tail)
    = (x, setSource str y, setSource str z) ::: setSources str tail

  export
  setSource : String -> Raw.Session -> Raw.Session
  setSource str (Null fc y)
    = Null (setSource     str fc)
           (setSourceNull str y)

  setSource str (Un fc y z)
    = Un (setSource str fc)
         y
         (setSource str z)

  setSource str (N1 fc y xs)
    = N1 (setSource  str fc)
         (setSourceN str y)
         (setSources1 str xs)

export
Show Raw.Session where

  show (Null x y) = "(NULL \{show x} \{show y})"
  show (Un x y z) = "(UN \{show x} \{show y} \{show z})"
  show (N1 x y xs) = "(N1 \{show x} \{show y} \{assert_total $ show xs})"


export
getFC : Raw.Session -> FileContext
getFC (Null x y) = x
getFC (Un x y z) = x
getFC (N1 x y xs) = x

-- [ EOF ]
