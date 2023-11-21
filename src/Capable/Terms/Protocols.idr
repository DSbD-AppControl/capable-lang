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
               -> (ss : List Session)
               -> (b  : Branch Global ks rs (s,t))
                     -> Type
      where
        B : {t : Base}
         -> (label  : String)
         -> (type   : Ty ts t)
         -> (choice : Global ks ts rs ss g)
                   -> Branch ks ts rs ss (B label t g)

    public export
    data Branches : (ks : List Kind)
                 -> (ts : List Base)
                 -> (rs : List Role)
                 -> (ss : List Session)
                 -> (b  : Global.Branches ks rs lts)
                       -> Type
      where
        Nil  : Branches ks ts rs ss Nil
        (::) : (b  : Branch   ks ts rs ss  b')
            -> (bs : Branches ks ts rs ss      bs')
                  -> Branches ks ts rs ss (b'::bs')


    public export
    data Global : (kinds : List Kind)
               -> (types : List Base)
               -> (roles : List Role)
               -> (ss : List Session)
               -> (type  : Global kinds roles)
                        -> Type
      where
        End : Global ks ts rs ss End

        Call : {v : _}
            -> (prf : RecVar ks v)
                   -> Global ks ts ss rs (Call prf)

        Rec : Global (v::ks) ts rs ss        type
           -> Global     ks  ts rs ss (Rec v type)

        Choice : {s,r : _}
              -> {f : (String,Base) }
              -> {fs : (List (String,Base))}
              -> {b  : Branch Global ks rs f}
              -> {bs : Global.Branches ks rs (fs)}
              -> (sender   : DeBruijn.Role rs s)
              -> (receiver : DeBruijn.Role rs r)
              -> (prf      : VarsNotEQ rs sender receiver)
--              -> (prf      : Not (REquals rs sender receiver))
              -> (type     : Ty ts (UNION (f:::fs)))
              -> (prfM     : Marshable (UNION (f:::fs)))
              -> (choices  : Branches ks ts rs ss (b::bs))
                          -> Global ks ts rs ss
                                    (ChoiceG sender
                                             receiver
                                             (Val (UNION (f:::fs)))
                                                  prfM
                                             prf
                                             (b::bs))

        -- Call outs
        ContAux : {ctzt : Context Role rs'}
               -> (idx  : IsVar ss (S ctzt global))
               -> (prf  : Prefix.Subset rs' rs)
                       -> Global ks ts rs ss (RecVar.weaken Empty (Role.weaken prf global))



export
getLabels : Branches ks ts rs ss bs -> List String
getLabels [] = []
getLabels ((B s type choice) :: x) = s :: getLabels x

-- [ EOF ]
