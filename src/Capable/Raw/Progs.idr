||| AST for Progs
|||
||| Module    : Raw/Progs.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
||| Let's be smart about the shape of the tree.
module Capable.Raw.Progs

import Toolkit.Data.Location
import Toolkit.AST

import Data.Vect.Quantifiers
import Capable.Types
import Capable.Raw.AST
import Capable.Raw.Role
import Capable.Raw.Protocols
import Capable.Raw.Types
import Capable.Raw.DTypes
import Capable.Raw.Exprs
import Capable.Raw.Funcs
import Capable.Raw.Sessions

%default total

public export
CalcDef : (kind : DefKind l) -> (AST l -> Type)
CalcDef DTYPE = DTy
CalcDef TYPE = Ty
CalcDef FUNC = Fun
CalcDef ROLE = Role
CalcDef PROT = Protocol
CalcDef SESH = Session

toDef : (x : DefKind k) -> (p : AST k) -> CalcDef x p
toDef DTYPE = toDType
toDef TYPE = toType
toDef FUNC = toFun
toDef ROLE = toRole
toDef PROT = toProtocol
toDef SESH = toSession

public export
data Prog : (p : PROG) -> Type
  where
    Main : (fc : FileContext)
        -> (m  : Fun f)
              -> Prog (Branch MAIN fc [f])

    Def : {rest : _}
       -> (fc    : FileContext)
       -> (what  : DefKind k)
       -> (s     : String)
       -> (val   : CalcDef what p)
       -> (scope : Prog rest)
                -> Prog (Branch (DEF s what) fc [p,rest])

export
toProg : (p : PROG) -> Prog p
toProg (Branch MAIN fc [f])
  = Main fc (toFun f)

toProg (Branch (DEF s x) fc [p,rest])
  = Def fc x s
             (toDef x p)
             (toProg rest)

-- [ EOF ]
