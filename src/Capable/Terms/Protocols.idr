||| Types as terms because we want to mirror real programmes.
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Capable.Terms.Protocols

import Decidable.Equality

import public Data.List.Elem

import public Data.List1

import public Toolkit.Data.DList

import public Capable.Types
import        Capable.Terms.Vars
import        Capable.Terms.Roles
import        Capable.Terms.Types

%default total
%hide type

namespace Global

  mutual
    public export
    data Branch : (ks : List Kind)
               -> (ts : List Base)
               -> (rs : List Role)
               -> (b  : Branch Global ks rs (s,t))
                     -> Type
      where
        B : {t : Base}
         -> (label  : String)
         -> (type   : Ty ts t)
         -> (choice : Global ks ts rs g)
                   -> Branch ks ts rs (B label t g)

    public export
    data Branches : (ks : List Kind)
                 -> (ts : List Base)
                 -> (rs : List Role)
                 -> (b  : Global.Branches ks rs lts)
                       -> Type
      where
        Nil  : Branches ks ts rs Nil
        (::) : (b  : Branch   ks ts rs  b')
            -> (bs : Branches ks ts rs      bs')
                  -> Branches ks ts rs (b'::bs')


    public export
    data Global : (kinds : List Kind)
               -> (types : List Base)
               -> (roles : List Role)
               -> (type  : Global kinds roles)
                        -> Type
      where
        End : Global ks ts rs End

        Call : (prf : RecVar ks)
                   -> Global ks ts rs (Call prf)

        Rec : Global (R::ks) ts rs      type
           -> Global     ks  ts rs (Rec type)

        Choice : {f : (String,Base) }
              -> {fs : (List (String,Base))}
              -> {b  : Branch Global ks rs f}
              -> {bs : Global.Branches ks rs (fs)}
--              -> {prfM : DList (String, Base) Marshable (f::fs)}
              -> (sender   : Role rs MkRole)
              -> (receiver : Role rs MkRole)
              -> (prf      : Not (Equals Role (IsVar rs) sender receiver))
              -> (type     : Ty ts (UNION (f:::fs)))
              -> (prfM     : Marshable (UNION (f:::fs)))
              -> (choices  : Branches ks ts rs (b::bs))
                          -> Global ks ts rs
                                    (Choice sender
                                            receiver
                                            (Val (UNION (f:::fs)))
                                                 prfM
                                            prf
                                            (b::bs))

-- [ EOF ]
