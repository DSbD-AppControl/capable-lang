||| How to run Ola programmes.
|||
||| Module    : Exec.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
|||
||| Inspired by:
|||
||| Casper Bach Poulsen, Arjen Rouvoet, Andrew Tolmach, Robbert
||| Krebbers, and Eelco Visser. 2017. Intrinsically-typed definitional
||| interpreters for imperative languages. Proc. ACM Program. Lang. 2,
||| POPL, Article 16 (January 2018), 34
||| pages. https://doi.org/10.1145/3158104
|||
||| but with some changes...
|||
module Ola.Exec

import Data.Vect
import Data.List.Elem
import Data.List.Quantifiers

import System.File

import Toolkit.Data.DList

import Ola.Core
import Ola.Terms
import Ola.Env
import Ola.Values

%default total

-- # Rug Adaptations

throw : Running.Error -> Ola a
throw = (throw . Exec)

panic : (why : String) -> Ola a
panic = (throw . Panic)

error : (why : FileError) -> Ola a
error = (throw . Outside)

todo : Ola a -- i know...
todo = throw NotYetImplemented

-- # Results
namespace Results

  namespace Expr
    public export
    data Result : (store : List Ty.Base) -> (type : Ty.Base) -> Type where
      Value : {new   : List Ty.Base}
           -> (store : Heap new)
           -> (value : Value new type)
           -> (prf   : Subset old new)
                    -> Result old type

    export
    return : {store : List Ty.Base}
          -> (heap  : Heap store)
          -> (value : Value store type)
                   -> Ola (Result store type)
    return heap value = pure (Value heap value (noChange _))

  namespace Stmt

    public export
    data Result : (stack, store : List Ty.Base)
               -> (type  : Ty.Base)
                        -> Type
      where
        ||| Captures the end of control flow that doesn't return a value
        Continue : {newH  : List Ty.Base}
                -> (env   : Env stack' newH)
                -> (store : Heap  newH)
                -> (prf   : Subset oldH newH )
                         -> Result stack' oldH type

        Value : {new   : List Ty.Base}
             -> (store : Heap  new)
             -> (val   : Value new type)
             -> (prf   : Subset old new )
                      -> Result stack old type

    export
    return : {store,store' : List Ty.Base}
          -> (prf  : Subset store store')
          -> (rest : Stmt.Result stack' store' b)
                  -> Ola (Stmt.Result stack' store b)
    return prf (Continue e h p)
      = pure (Continue e h (trans prf p))

    return prf (Value h val p)
      = pure (Value h val (trans prf p))

    export
    return2 : {store,store',store'' : List Ty.Base}
           -> (p1   : Subset store  store')
           -> (p2   : Subset store' store'')
           -> (rest : Stmt.Result stack store'' b)
                   -> Ola (Stmt.Result stack store b)
    return2 p1 p2 rest
      = do res <- return p2 rest
           return p1 res

  namespace Args

    public export
    data Results : (store : List Ty.Base)
                -> (types : List Ty.Base)
                         -> Type
      where
        Args : {new   : List Ty.Base}
            -> (store : Heap  new)
            -> (args  : DList Ty.Base (Value new) types)
            -> (prf   : Subset  old new )
                     -> Results old types

||| An API to support expressions that interact with the heap.
namespace Heap
  namespace Expr
    export
    insert : {store : List Ty.Base}
          -> {type  : Ty.Base}
          -> (value : Value store type)
          -> (heap  : Heap  store)
                   -> Ola (Expr.Result store (REF type))
    insert {store} {type} v h
      = let new = snoc_add type store              -- Extend type-level context
        in let v' = Address (snoc_elem store type) -- Generate address
        in let h' = snoc (map (weaken new) h)      -- Update heap
                         (weaken new v)
        in pure (Value h' v' new)

    export
    fetch : {store : List Ty.Base}
         -> (loc   : IsVar  store type)
         -> (heap  : Heap store)
                  -> Ola (Expr.Result store type)
    fetch loc heap
      = let val = Heap.lookup loc heap
        in pure (Value heap val (noChange _))

  namespace Stmt
    export
    mutate : {store : List Ty.Base}
          -> (what  : IsVar store type)
          -> (heap  : Heap store)
          -> (with_ : Val type store)
                   -> Heap store

    mutate what heap with_
      = Heap.replace what with_ heap


debase : FileError -> Nat
debase (GenericFileError i) = minus (cast {to=Nat} i) 5
debase FileReadError = 0
debase FileWriteError = 1
debase FileNotFound = 2
debase PermissionDenied = 3
debase FileExists = 4



-- # Executing stuff

mutual
  ||| Executing Expressions
  namespace Exprs
    %inline
    when : {type : Ty.Base}
        -> (env  : Env stack store)
        -> (cond : Expr.Result store BOOL)
        -> (tt   : Expr roles types stack type)
        -> (ff   : Expr roles types stack type)
                -> Ola (Expr.Result store type)

    when env (Value h (B False) prf) _ ff
      = do Value hf vf prfF <- Exprs.eval (weaken prf env) h ff
           pure (Value hf vf (trans prf prfF))

    when env (Value h (B True) prf) tt _
      = do Value hf vf prfF <- Exprs.eval (weaken prf env) h tt
           pure (Value hf vf (trans prf prfF))



    public export
    eval : {type  : Ty.Base}
        -> {store : List Ty.Base}
        -> (env   : Env              stack store)
        -> (heap  : Heap                   store)
        -> (expr  : Expr roles types stack       type)
                 -> Ola (Expr.Result store type)
    -- Variables
    eval env heap (Var x)
      = return heap
               (read x env)

    -- ### Constants
    eval env heap U     = return heap U
    eval env heap (C x) = return heap (C x)
    eval env heap (S x) = return heap (S x)
    eval env heap (I x) = return heap (I x)
    eval env heap (B x) = return heap (B x)

    -- ### Ternary operations.
    eval env heap (Cond cond tt ff)
      = do res <- eval env heap cond
           when env res tt ff

    -- ### Array's & Operations
    eval env heap ArrayEmpty = return heap ArrayEmpty

    eval env heap (ArrayCons x xs)
      = do Value h'  x  p1 <- eval env heap x
           Value h'' xs p2 <- eval (weaken p1 env) h'   xs

           pure (Value h'' (ArrayCons (weaken p2 x) xs) (trans p1 p2))


    eval env heap (Index idx array)
        = do Value h' xs p1 <- eval env heap array
             let x = index idx xs
             pure (Value h' x p1)

    -- ### Data Structures

    eval env heap (Pair x y)
      = do Value h'  l p1 <- eval            env  heap x
           Value h'' r p2 <- eval (weaken p1 env) h'   y
           pure (Value h''
                       (Pair (weaken p2 l)
                             r)
                       (trans p1 p2))

    eval env heap (Left x)
      = do Value h' x p1 <- eval env heap x
           pure (Value h' (Left x) p1)

    eval env heap (Right x)
      = do Value h' x p1 <- eval env heap x
           pure (Value h' (Right x) p1)

    -- ### References

    eval env heap (Fetch x)
      = do Value h' (Address x) prf <- eval env heap x

           Value h'' v pr2 <- fetch x h'

           pure (Value h'' v (trans prf pr2))

    eval env heap (Alloc x)
      = do Value h'  res prf  <- eval env heap x
           Value h'' ref prf2 <- insert res h'

           pure (Value h'' ref (trans prf prf2))

    -- ### File/Process Interactions
    eval env heap (Open k m fname) with (k)
      eval env heap (Open k m fname) | FILE
        = do Value h (S fname) prf <- eval env heap fname
             val <- embed (openFile fname m)
             case val of
               Left err =>
                 do let e = debase err
                    pure (Value h (Left (I e)) prf)
               Right fh =>
                 do pure (Value h (Right (H FILE fh)) prf)

      eval env heap (Open k m fname) | PROCESS
        = do Value h (S fname) prf <- eval env heap fname
             val <- embed (popen fname m)
             case val of
               Left err =>
                 do let e = debase err
                    pure (Value h (Left (I e)) prf)
               Right fh =>
                 pure (Value h (Right (H PROCESS fh)) prf)

    eval env heap (ReadLn x)
      = do Value h (H k fh) prf <- eval env heap x
           res <- embed (fGetLine fh)
           case res of
             Left err =>
               do let e = debase err
                  pure (Value h (Left (I e)) prf)
             Right str =>
               pure (Value h (Right (S str)) prf)

    eval env heap (WriteLn k s)
      = do Value h  (H k fh) prf  <- eval env heap k
           Value h' (S str)  prf' <- eval (weaken prf env) h s

           res <- embed (fPutStrLn fh str)
           case res of
             Left err =>
               do let e = debase err
                  pure (Value h' (Left (I e)) (trans prf prf'))
             Right str =>
               pure (Value h' (Right U) (trans prf prf'))

    eval env heap (Close x)
      = do Value h (H k fh) prf <- eval env heap x
           case k of
             PROCESS
               => do v <- embed (pclose fh)
                     pure (Value h U prf)

             FILE
               => do v <- embed (closeFile fh)
                     pure (Value h U prf)


    -- ### Function Calls

    eval env heap (Call f xs)
           -- Fetch closure
      = do Value h (Clos scope clos) prf <- eval env  heap f

           -- Evaluate args
           Args h args p1 <- Args.eval (weaken prf env) h xs

           -- Call function
           Value h v p2   <- Func.eval (weaken p1 clos) h scope args

           pure (Value h
                       v
                       (trans prf (trans p1 p2)))

    -- ### Annotations

    eval env heap (The _ expr)
      = eval env heap expr

  namespace Args
    export
    eval : {as,store : List Ty.Base}
        -> (env   : Env        stack store)
        -> (heap  : Heap             store)
        -> (args  : DList Ty.Base (Expr rs tys stack) as)
                 -> Ola (Args.Results store as)
    eval env heap []
      = pure (Args heap
                   Nil
                   (noChange _))

    eval env heap (x :: xs)
      = do Value h v  p <- eval env heap x
           Args  h vs ps <- eval (weaken p env) h xs
           pure (Args h
                      ((weaken ps v)::vs)
                      (trans p ps))
  ||| Executing a Statement
  namespace Stmt

    ||| Bespoke join to ensure early returns
    join : {type : Ty.Base}
        -> {store : List Ty.Base}
        -> (env   : Env stack store)
        -> (this  : Stmt.Result stack'' store type)
        -> (stmt  : Stmt roles types stack stack' type)
                 -> Ola (Stmt.Result stack' store type)
    join e (Continue _ h prf) stmt
      = do res <- (eval (weaken prf e) h stmt)
           return prf res

    join _ (Value h val prf) _
      = pure (Value h val prf)

    ||| Expressions return values, statements may return early.
    public export
    eval : {type : Ty.Base}
        -> {store : List Ty.Base}
        -> (env   : Env stack store)
        -> (heap  : Heap store)
        -> (stmt  : Stmt roles types stack out type)
                 -> Ola (Stmt.Result out store type)

    -- ### Bindings
    eval env heap (Let _ expr rest)
      = do Value h v p <- eval env heap expr
           res <- eval (v::weaken p env) h rest
           return p res

    -- ### Mutations
    eval env heap (Mutate loc value rest)
      = do Value h (Address adr) p1 <- eval            env  heap loc
           Value h nu            p2 <- eval (weaken p1 env) h    value
           let h' = mutate (expand adr p2) h nu

           res <- eval (weaken p2 $ weaken p1 env) h' rest

           return2 p1 p2 res

    -- ### Run side-effecting programs.
    eval env heap (Run expr rest)
      = do Value h _ p <- eval env heap expr
           res <- eval (weaken p env) h rest
           return p res

    -- ### Conditionals
    eval env heap (Cond cond tt ff rest)
      = do Value h v p <- eval env heap cond
           case v of
             B True
               => do t <- eval (weaken p env) h tt
                     r <- join (weaken p env) t rest
                     return p r

             B False
               => do t <- eval (weaken p env) h ff
                     r <- join (weaken p env) t rest
                     return p r

    -- ### Matching
    eval env heap (Match expr left right rest)
      = do Value h v p <- eval env heap expr
           case v of
             Left l
               => do l <- eval (l::weaken p env) h left
                     r <- join (weaken p env) l rest
                     return p r

             Right r
               => do l <- eval (r::weaken p env) h right
                     r <- join (weaken p env) l rest
                     return p r

    eval env heap (Split expr rest)
      = do Value h (Pair a b) p <- eval env heap expr
           r <- eval (b::a::weaken p env) h rest
           return p r

    -- ## While Loops
    eval env heap (While expr body rest)
      = do Value h c p <- eval env heap expr
           case c of
             B True -- Satisfied, loop
               => do r <- eval (weaken p env) h body
                     r <- join (weaken p env) r (While expr body rest)
                     return p r
             B False -- Return
               => do r <- eval (weaken p env) h rest
                     return p r

    -- ### Printing
    eval env heap (Print this rest)
      = do Value h (S t) p <- eval env heap this
           putStrLn t
           res <- eval (weaken p env) h rest
           return p res

    -- ### End of computations...
    eval env heap End
      = pure (Continue env heap (noChange _))

    eval env heap (Return expr)
      = do Value h v p <- eval env heap expr
           pure (Value h v p)

  namespace Func
    ||| Let's deal with functions separatly.
    public export
    eval : {store : List Ty.Base}
        -> {as    : List Ty.Base}
        -> {ret : Ty.Base}
        -> (env   : Env              stack store)
        -> (heap  : Heap                   store)
        -> (func  : Func roles types stack          (FUNC as ret))
        -> (vals  : DList Ty.Base (Value store) as)
                 -> Ola (Expr.Result store ret)

    eval env heap (Fun body last) args
      = do res <- eval (extend args env) heap body
           case res of
             Continue e h p
               => do Value h v p' <- eval e h last
                     pure (Value h v (trans p p'))
             Value h v p => pure (Value h v p)


namespace Progs

  mutual
    ||| We need to extract the type-level type.
    |||
    ||| Although we could 'depend' on the 'implicit' type-level type,
    ||| calculating this might be a better way.  I am not sure, and
    ||| can be changed....
    public export
    resolve : (env : Env types)
           -> (ty  : Ty types type)
                  -> Singleton type
    resolve env TyChar
      = Val CHAR
    resolve env TyStr
      = Val STR
    resolve env TyInt
      = Val INT
    resolve env TyBool
      = Val BOOL
    resolve env (TyArray tmType nat)
      = let Val i = (resolve env tmType)
        in Val (ARRAY i nat)

    resolve env (TyPair tmA tmB)
      = let Val a = resolve env tmA
        in let Val b = resolve env tmB
        in Val (PAIR a b)

    resolve env (TyUnion tmA tmB)
      = let Val a = resolve env tmA
        in let Val b = resolve env tmB
        in Val (UNION a b)

    resolve env TyUnit
      = Val UNIT

    resolve env (TyRef tmType)
      = let Val a = (resolve env tmType)
        in Val (REF a)

    resolve env (TyHandle kind)
      = Val (HANDLE kind)

    resolve env (TyFunc tmA tmB)
      = let Val args = resolves env tmA
        in let Val ret = resolve env tmB
        in Val (FUNC args ret)

    resolve env (TyVar x)
      = (read x env)

    resolves : (env : Env types)
            -> (ty  : DList Ty.Base (Ty types) tys)
                   -> Singleton tys
    resolves env [] = Val []
    resolves env (x :: xs)
      = let Val x  = resolve  env x in
        let Val xs = resolves env xs
        in Val (x::xs)

  ||| Run a programme.
  public export
  run : {type : Ty.Base}
      -> {store : List Ty.Base}
      -> (envR  : Env roles)
      -> (envT  : Env types)
      -> (env   : Env        stack store)
      -> (heap  : Heap             store)
      -> (expr  : Prog roles types stack   type)
               -> Ola (Expr.Result store type)

  run er et env heap (DefSesh s scope)
    = run er et env heap scope

  run er et env heap (DefRole rest)
    = do run (Val MkRole::er)
             et
             env
             heap
             rest



  -- Typedefs need resolving.
  run er et env heap (DefType tyRef rest)
    = do let ty = resolve et tyRef
         run er
             (ty::et)
             env
             heap
             rest


  -- Functions store their environment at time of definition.
  run er et env heap (DefFunc sig func rest)
    = run er
          et
          (Clos func env :: env)
          heap
          rest


  -- The main sh-bang
  run _ _ env heap (Main x)
    = eval env heap x Nil

||| Only run closed programmes.
export
exec : (prog : Program)
            -> Ola ()

exec p
  = do ignore (run Nil Nil Nil Nil p)
       pure ()

-- [ EOF ]
