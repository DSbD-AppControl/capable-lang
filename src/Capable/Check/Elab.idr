||| Elaborator to datatypes into core terms.
|||
||| 1. Structs get turned into 'newtypes', and have accessor methods created.
||| 2. Unions have methods generated to create instances.
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Capable.Check.Elab

import Data.List.Views
import Data.String

import Toolkit.Data.Location

import Capable.Types
import Capable.Core

import Capable.Raw.AST
import Capable.Raw.Types
import Capable.Raw.DTypes
import Capable.Raw.Exprs
import Capable.Raw.Funcs
import Capable.Raw.Role
import Capable.Raw.Progs

%default total

-- # Higher ORder Functions to generate projections of fields in a datatype.

||| Higher ORder Function to generate user defined projections of fields in a datatype.
projs : {t, fields' : _}
     -> (f : {t,t' : _}
          -> FileContext
          -> Ty t
          -> String
          -> Ty t'
          -> (DPair FUNC (\f => (FileContext, String, Fun f))))
     -> Ty t
     -> Named.Args fields'
     -> List (DPair FUNC (\f => (FileContext, String, Fun f)))
projs f atype Nil = Nil
projs f atype (Add fc' s t xs)
  = f fc' atype s t :: projs f atype xs

||| Fold a set of projections into a given scope.
foldFun : (DPair FUNC (\f => (FileContext, String, Fun f)))
        -> DPair PROG Prog
        -> DPair PROG Prog
foldFun (f' ** (fc,label,fn)) (p' ** scope)
  = (_ ** Def fc FUNC label fn scope)

-- # Elaboration of Recoreds

||| Generate a getter to access a valid element of the record.
|||
|||
|||
||| In concrete syntax this is:
|||
||| ```
||| func get_x(label : struct { x : t; ...}) -> t { get[x](label) }
||| ```
|||
projGet : {t,t' : _}
       -> FileContext
       -> Ty t
       -> String
       -> Ty t'
       -> (DPair FUNC (\f => (FileContext, String, Fun f)))
projGet fc atype str rtype
  = (_ ** ( fc
          , "get_" ++ str
          , Func {fc' = fc}
               fc
               (Next Empty)
               [A fc "label" atype]
               rtype
               (GetR fc str (Var (MkRef fc "label") R))))

||| Generate a setter to set a valid element of the record.
|||
|||
|||
||| In concrete syntax this is:
|||
||| ```
||| func set_x(rec : struct { x : t; ...}, val : t) -> struct { x : t; ...} { set[x](rec, val) }
||| ```
|||
projSet : {t,t' : _}
       -> FileContext
       -> Ty t
       -> String
       -> Ty t'
       -> (DPair FUNC (\f => (FileContext, String, Fun f)))
projSet fc atype str rtype
  = (_ ** ( fc
          , "set_" ++ str
          , Func {fc' = fc}
               fc
               (Next (Next Empty))
               [A fc "rec" atype, A fc "val" rtype ]
               atype
               (SetR fc
                     str
                     (Var (MkRef fc "rec") R)
                     (Var (MkRef fc "val") R))))

-- ## Utilities to generate arguments and references when projecting records.

data PArgs : Vect n FIELD -> Type where
  PA : {fs : Vect n FIELD}
    -> {as : _}
    -> {vs : Vect n ARG}
    -> (prf : AsVect as vs)
    -> (val : All Arg vs)
           -> PArgs fs

||| Generate arguments used within a record construction function
projArgs : {f : _}
        -> {fields : Vect n FIELD}
        -> Named.Args (f::fields)
        -> PArgs (f::fields)

projArgs (Add fc s ty Nil)
  = PA (Next Empty)
       ((A fc s ty ) :: All.Nil)

projArgs (Add fc s ty (Add fc' s' ty' rest))
  = let (PA prf tms) = projArgs (Add fc' s' ty' rest)
    in PA (Next prf)
          (A fc s ty :: tms)

data PRefs : Vect n FIELD -> Type where
  PR : {fs : Vect n FIELD}
    -> {as : _}
    -> {vs : Vect n FIELDV}
    -> (prf : AsVect as vs)
    -> (val : All Field vs)
           -> PRefs fs

||| Generate references used within a record construction function.
projRefs : {f : _}
        -> {fields : Vect n FIELD}
        -> Named.Args (f :: fields)
        -> PRefs (f::fields)

projRefs (Add fc s ty Nil)
  = PR (Next Empty)
       ((F fc s (Var (MkRef fc s) R) ):: All.Nil)

projRefs (Add fc s _ (Add fc' s' ty' rest))
  = let PR prf tms = projRefs (Add fc' s' ty' rest)
    in  PR (Next prf)
           (F fc s (Var (MkRef fc s) R) :: tms)

||| Generate a record constructor as a function.
|||
||| Assuming:
|||
||| ```
||| struct Foo { x : t; ...}
||| ```
|||
||| and
|||
||| ```
||| let Foo = struct { x : t; ...}
||| ```
|||
||| then
|||
||| ```
||| func Foo(x : t, ...) { MkRecord { x, ...} }
||| ```
projCtor : {t, f,fields' : _}
        -> FileContext
        -> String
        -> Ty t
        -> Named.Args (f::fields')
        -> (DPair FUNC (\f => (FileContext, String, Fun f)))
projCtor fc n rtype argso
   = let PA pa args = projArgs argso in
     let PR pr refs = projRefs argso
     in (_ ** ( fc
              , n
              , Func {fc' = fc}
                   fc
                   pa
                   args
                   rtype
                   (Record fc pr (refs))
               ))

||| Generate accessors and encapsulate records.
|||
||| Thus we are transforming:
|||
||| ```
||| struct foo { x : t ; ... ; y : s}
|||
||| body
||| ```
|||
||| assuming:
|||
||| ```
||| let foo = struct {x : t ; ... } in body
||| ```
|||
||| into
|||
||| ```
||| func x(value : t) -> foo { the foo tag[x](value) }
|||
||| ...
|||
||| body
||| ```
export
generateProjections : {t,f,fields,p : _ }
                   -> FileContext
                   -> String
                   -> Ty t
                   -> Named.Args (f::fields)
                   -> Prog p
                   -> DPair PROG Prog
generateProjections fc n rtype fs scope
  = let gs = projs projGet rtype fs in
    let ss = projs projSet rtype fs in
    let ctor = projCtor fc n rtype fs
    in foldr foldFun (_ ** scope) (ctor :: gs ++ ss)

-- ## Unions

||| Generate a method to construct a valid element of the union.
|||
|||
|||
||| In concrete syntax this is:
|||
||| ```
||| func x(value : t) -> union { x : t; ...} { the (union { x : t; ...}) tag[x](value) }
||| ```
|||
projTag : {t,t' : _}
       -> FileContext
       -> Ty t
       -> String
       -> Ty t'
       -> (DPair FUNC (\f => (FileContext, String, Fun f)))
projTag fc atype str rtype
  = (_ ** ( fc
          , str
          , Func {fc' = fc}
               fc
               (Next Empty)
               [A fc "value" rtype]
               atype
               (The fc atype (Tag fc str (Var (MkRef fc "value") R)))

               ))

||| Generate ctors for each tag in a union.
|||
||| Thus we are transforming:
|||
||| ```
||| union foo { x : t ; ... }
|||
||| body
||| ```
|||
||| assuming:
|||
||| ```
||| let foo = union {x : t ; ... ; y : s} in body
||| ```
|||
||| into
|||
||| ```
||| func x(value : t) -> foo { the foo tag[x](value) }
|||
||| ...
|||
||| body
||| ```
export
generateTags : {t,fields,p : _ } -> Ty t -> Named.Args fields -> Prog p -> DPair PROG Prog
generateTags rtype fs scope
  = let gs = projs projTag rtype fs
    in foldr foldFun (_ ** scope) gs

-- [ EOF ]
