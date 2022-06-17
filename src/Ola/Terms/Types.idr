||| Types as terms because we want to mirror real programmes.
|||
||| Module    : Types.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
module Ola.Terms.Types

import public Data.List.Elem

import public Ola.Types
import        Ola.Terms.Vars

%default total

||| A Type as a Term.
|||
||| This enables us to capture, in a simply way, type-synonms as
||| intrinsically typed terms.
|||
||| Will this provide support for polymorphic data structures,
||| newtypes, and polymorphic functions, probably not.
|||
||| But that is a different set of research engineering issues.
public export
data Ty : (context : List Ty)
       -> (type    : Ty)
                  -> Type
  where
    TyChar : Ty ctxt CHAR
    TyStr  : Ty ctxt STR
    TyInt  : Ty ctxt INT
    TyBool : Ty ctxt BOOL

    TyArray : (tmType : Ty ctxt type)
           -> (nat    : Nat)
                     -> Ty ctxt (ARRAY type nat)

    TyPair : (tmA : Ty ctxt a)
          -> (tmB : Ty ctxt b)
                 -> Ty ctxt (PAIR a b)

    TyUnion :(tmA : Ty ctxt a)
          -> (tmB : Ty ctxt b)
                 -> Ty ctxt (UNION a b)

    TyUnit : Ty ctxt UNIT

    TyRef : (tmType : Ty ctxt type)
                   -> Ty ctxt (REF type)

    TyHandle : (kind : HandleKind)
                    -> Ty ctxt (HANDLE kind)

    TyFunc : (tmA : Ty ctxt a)
          -> (tmB : Ty ctxt b)
                 -> Ty ctxt (FUNC a b)

    TyVar : Var ctxt type
         -> Ty  ctxt type

-- [ EOF ]
