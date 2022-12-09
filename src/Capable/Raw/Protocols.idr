||| AST for Global MPST by being a views on the AST.
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Capable.Raw.Protocols

import Data.Vect
import Data.Vect.Quantifiers

import Toolkit.Data.DVect

import Toolkit.Data.Location

import Capable.Types
import Capable.Raw.AST
import Capable.Raw.Role
import Capable.Raw.Types

%default total

mutual

  public export
  data Branches1 : (bs : Vect (S n) (AST BRANCH))
                -> Type
    where
      B1 : All Branch (b::bs)
        -> Branches1 (b::bs)

  public export
  data Branch : (b : Raw.AST.BRANCH)
                  -> Type
    where
      B : (fc    : FileContext)
       -> (label : String)
       -> (type  : Ty t)
       -> (cont  : Protocol c)
                -> Branch (Branch (BRANCHP label)
                          fc
                          [t,c])

  public export
  data Protocol : (r : Raw.AST.PROT)
                     -> Type
    where
      End : (fc : FileContext)
               -> Protocol (Branch STOP fc Nil)

      Call : (fc  : FileContext)
          -> (r   : Ref)
          -> (prf : AsRef s fc r)
                 -> Protocol (Branch (CALLP s) fc Nil)

      Rec : (fc : FileContext)
         -> (r  : Ref)
         -> (prf : AsRef s fc r)
         -> (scope : Protocol b)
                  -> Protocol (Branch (RECP s) fc [b])

      Choice : (fc : FileContext)
            -> (s  : Role sr)
            -> (r  : Role rr)
            -> (t  : Ty tt)
            -> (prf : AsVect bs vs)
            -> (branches : Branches1 vs)
                        -> Protocol (Branch CHOICE fc (sr::rr::tt::bs))

mutual
  toBranch : (b : Raw.AST.BRANCH)
               -> Branch b
  toBranch (Branch (BRANCHP l) fc [t,c])
    = B fc l (toType t)
             (toProtocol c)

  toBranches : (bs : Vect n Raw.AST.BRANCH)
                  -> All Branch bs
  toBranches [] = []
  toBranches (x :: xs)
    = toBranch x :: toBranches xs


  export
  toProtocol : (r : Raw.AST.PROT)
                 -> Protocol r
  toProtocol (Branch STOP fc Nil)
    = End fc

  toProtocol (Branch (CALLP str) fc Nil)
    = Call fc (MkRef fc str) R

  toProtocol (Branch (RECP str) fc [c])
    = Rec fc (MkRef fc str) R (toProtocol c)

  toProtocol (Branch CHOICE fc (s::r::t::nodes))
    = let ((v::vs) ** prf) = asVect nodes
      in Choice fc
                (toRole s)
                (toRole r)
                (toType t)
                prf
                (B1 $ assert_total
                    $ toBranches (v::vs))

-- [ EOF ]
