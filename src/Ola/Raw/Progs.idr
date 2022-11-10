||| AST for Progs
|||
||| Module    : Raw/Progs.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
||| Let's be smart about the shape of the tree.
module Ola.Raw.Progs

import Toolkit.Data.Location
import Toolkit.AST

import Data.Vect.Quantifiers
import Ola.Types
import Ola.Raw.AST
import Ola.Raw.Role
import Ola.Raw.Protocols
import Ola.Raw.Types
import Ola.Raw.Exprs
import Ola.Raw.Funcs

%default total

public export
CalcDef : (kind : DefKind l) -> (AST l -> Type)
CalcDef TYPE = Ty
CalcDef FUNC = Fun
CalcDef ROLE = Role
CalcDef PROT = Protocol

toDef : (x : DefKind k) -> (p : AST k) -> CalcDef x p
toDef TYPE = toType
toDef FUNC = toFun
toDef ROLE = toRole
toDef PROT = toProtocol

public export
data Prog : (p : PROG) -> Type
  where
    Main : (fc : FileContext)
        -> (m  : Fun f)
              -> Prog (Branch MAIN fc [f])

    Def : (fc    : FileContext)
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
