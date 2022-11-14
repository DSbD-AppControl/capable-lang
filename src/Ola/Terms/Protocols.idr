||| Types as terms because we want to mirror real programmes.
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Ola.Terms.Protocols

import Decidable.Equality

import public Data.List.Elem

import public Data.List1

import public Toolkit.Data.DList

import public Ola.Types
import        Ola.Terms.Vars
import        Ola.Terms.Roles
import        Ola.Terms.Types

%default total
%hide type

namespace Global

  mutual
    public export
    data Branch : (ks : List Kind)
               -> (ts : List Base)
               -> (rs : List Role)
               -> (b  : Global.Branch ks rs)
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
                 -> (b  : Global.Branches ks rs)
                       -> Type
      where
        Nil  : Branches ks ts rs Nil
        (::) : (b  : Branch   ks ts rs  b')
            -> (bs : Branches ks ts rs      bs')
                  -> Branches ks ts rs (b'::bs')

    public export
    data Branches1 : (ks : List Kind)
                  -> (ts : List Base)
                  -> (rs : List Role)
                  -> (b  : Global.Branches1 ks rs)
                        -> Type
      where
        Bs1 : (bs : Branches  ks ts rs (b':: bs'))
                 -> Branches1 ks ts rs (b':::bs')

    public export
    data Global : (kinds : List Kind)
               -> (types : List Base)
               -> (roles : List Role)
               -> (type  : Global kinds roles)
                        -> Type
      where
        End : Global ks ts rs End
        Call : (prf : IsVar ks R) -> Global ks ts rs (Call prf)

        Rec : Global (R::ks) ts rs      type
           -> Global     ks  ts rs (Rec type)

        Choice : (sender   : Role rs MkRole)
              -> (receiver : Role rs MkRole)
              -> (prf              : Not (Equals Role (IsVar rs) sender receiver))
              -> (choices          : Branches1 ks ts rs bs)
                                  -> Global ks ts rs (Choice sender receiver prf bs)

-- [ EOF ]
