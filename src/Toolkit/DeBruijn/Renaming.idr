||| How to rename things
|||
||| Module    : Renaming.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
module Toolkit.DeBruijn.Renaming

import Decidable.Equality
import Data.DPair

import Toolkit.Decidable.Informative

import Toolkit.Data.List.AtIndex
import Toolkit.Data.DList
import Toolkit.Data.DList.AtIndex

import Toolkit.DeBruijn.Context.Item
import Toolkit.DeBruijn.Context

%default total

public export
data IsVar : (ctxt : List kind)
          -> (type :      kind)
                  -> Type
  where
    V : (  pos : Nat)
     -> (0 prf : AtIndex type ctxt pos)
              -> IsVar   ctxt type

public export
%inline
shift : IsVar ctxt type -> IsVar (ctxt += a) type
shift (V pos prf) = V (S pos) (There prf)

public export
%inline
weaken : (func : IsVar old type
              -> IsVar new type)
      -> (IsVar (old += type') type
       -> IsVar (new += type') type)
weaken f (V Z Here)
  = V Z Here
weaken f (V (S idx) (There later)) with (f (V idx later))
  weaken f (V (S idx) (There later)) | (V pos prf)
    = V (S pos) (There prf)

public export
interface Rename (type : Type) (term : List type -> type -> Type) | term where
  rename : {old, new : List type}
        -> (f : {ty : type} -> IsVar old ty
                            -> IsVar new ty)
        -> ({ty : type} -> term old ty
                        -> term new ty)

  %inline
  embed : {ty   : type}
       -> {ctxt : List type}
               -> IsVar ctxt ty
               -> term  ctxt ty

public export
%inline
weakens : {type : Type}
       -> {term : List type -> type -> Type}
       -> Rename type term
       => {old, new : List type}
       -> (f : {ty  : type}
                   -> IsVar old ty
                   -> term  new ty)
       -> ({ty,type' : type}
              -> IsVar (old += type') ty
              -> term  (new += type') ty)

weakens f (V 0 Here)
  = embed (V Z Here)
weakens f (V (S idx) (There later))
  = rename shift (f (V idx later))

-- [ EOF ]
