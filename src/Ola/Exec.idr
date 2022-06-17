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
module Ola.Exec

import Data.Vect
import Data.List.Elem
import Data.List.Quantifiers

import Toolkit.Data.DList

import Ola.Core
import Ola.Terms
import Ola.Env
import Ola.Values

%default total

-- Adapting the Rug for this specific section.

throw : Running.Error -> Ola a
throw = (throw . Exec)

panic : (why : String) -> Ola a
panic = (throw . Panic)

error : (why : FileError) -> Ola a
error = (throw . Outside)

todo : Ola a -- i know...
todo = throw NotYetImplemented

||| Use a custom type to capture the values and heap changes.
public export
data Result : (val   : List Ty -> Ty -> Type)
           -> (type  : Ty)
           -> (store : List Ty)
                    -> Type
  where
    R : {new   : List Ty}
     -> (store : Heap  new)
     -> (val   : valTy new     type)
     -> (prf   : Subset old new)
              -> Result valTy type old

-- An API to interact with the heap in the computation context we are working with.

insert : {store' : List Ty}
     -> {type   : Ty}
     -> Value store' type
     -> Heap store'
     -> Ola (Result Value (REF type) store')
insert {store'} {type} v h
  = let new = snoc_add type store'
    in let v'  = Address (snoc_elem store' type)
    in let h'  = snoc (map (weaken new) h)
                      (weaken new v)

    in pure $ R h' v' new

fetch : {store : List Ty}
     -> (loc   : Var  store type)
     -> (heap  : Heap store)
              -> Ola (Result Value type store)
fetch loc heap
  = let val = Heap.lookup loc heap
    in pure (R heap val (noChange _))


mutate : {store : List Ty}
      -> (what  : Var store type)
      -> (heap  : Heap store)
      -> (with_ : Val type store)
               -> Ola (Result Value UNIT store)
mutate what old with_
  = let new = Heap.replace what with_ old
    in pure (R new U (noChange _))

-- # Executing stuff

mutual
  ||| Executing Expressions
  namespace Exprs

    public export
    eval : {type : Ty}
        -> {store : List Ty}
        -> (env   : Env        stack store)
        -> (heap  : Heap             store)
        -> (expr  : Expr types stack          type)
                 -> Ola (Result Value type store)

    -- ### Variables
    eval env heap (Var x)
      = let v = DList.lookup x env
        in pure (R heap v (noChange _))

    -- ### Constants.
    eval env heap U     = pure (R heap U     (noChange _))
    eval env heap (C x) = pure (R heap (C x) (noChange _))
    eval env heap (S x) = pure (R heap (S x) (noChange _))
    eval env heap (I x) = pure (R heap (I x) (noChange _))
    eval env heap (B x) = pure (R heap (B x) (noChange _))

    -- ### Ternary operations.
    eval env heap (Cond cond tt ff)
      = do R h' v prf <- eval env heap cond
           case v of
             (B False) => do R h'' v' prf' <- eval (weaken prf env) h' ff
                             pure (R h'' v' (trans prf prf'))

             (B True)  => do R h'' v' prf' <- eval (weaken prf env) h' tt
                             pure (R h'' v' (trans prf prf'))

    -- ### Array's & Operations
    eval env heap ArrayEmpty
      = pure (R heap ArrayEmpty (noChange _))

    eval env heap (ArrayCons x xs)
      = do R h'  x  p1 <- eval env heap x
           R h'' xs p2 <- eval (weaken p1 env) h'  xs

           pure (R h'' (ArrayCons (weaken p2 x) xs) (trans p1 p2))

    eval env heap (Index idx array)
      = do R h' xs p1 <- eval env heap array
           let x = index idx xs
           pure (R h' x p1)


    -- ### Pairs and operations

    eval env heap (Pair x y)
      = do R h'  l p1 <- eval            env  heap x
           R h'' r p2 <- eval (weaken p1 env) h'   y
           pure (R h'' (Pair (weaken p2 l) r) (trans p1 p2))

    eval env heap (First x)
      = do R h' (Pair l r) p1 <- eval env heap x
           pure (R h' l p1)

    eval env heap (Second x)
      = do R h' (Pair l r) p1 <- eval env heap x
           pure (R h' r p1)

    -- ### Unions and their operations
    eval env heap (Left x)
      = do R h' x p1 <- eval env heap x
           pure (R h' (Left x) p1)

    eval env heap (Right x)
      = do R h' x p1 <- eval env heap x
           pure (R h' (Right x) p1)

    eval env heap (Match expr left right)
      = do R h' e p1 <- eval env heap expr
           case e of
             (Left x)
               => do R h'' res p2 <- eval (x::(weaken p1 env))
                                          h'
                                          left
                     pure (R h'' res (trans p1 p2))
             (Right x)
               => do R h'' res p2 <- eval (x::(weaken p1 env))
                                           h'
                                           right
                     pure (R h'' res (trans p1 p2))

    -- ### References
    eval env heap (Fetch x)
      = do R h' (Address x) prf <- eval env heap x
           R h'' v pr2 <- fetch x h'
           pure (R h'' v (trans prf pr2))

    eval env heap (Alloc x)
      = do R h'  res prf <- eval env heap x
           R h'' ref prf2 <- insert res h'
           pure (R h'' ref (trans prf prf2))

    eval env heap (Mutate l e)
      = do R h'   (Address l') prf1 <- eval env heap l
           R h''  e'           prf2 <- eval (weaken prf1 env) h' e
           R h''' U            prf3 <- mutate (expand l' prf2) h'' e'

           pure (R h''' U (trans prf1 (trans prf2 prf3)))

    -- ### File/Process Interactions
    eval env heap (Open what x)
      = todo
    eval env heap (ReadLn x)
      = todo
    eval env heap (WriteLn x y)
      = todo
    eval env heap (Close x)
      = todo

    -- ### Function Calls
    eval env heap (Call f a)
      = do R h  (Clos scope clos) prf   <- eval             env  heap f
           R h' a                 prf1  <- eval (weaken prf env) h    a
           R h'' res prf2 <- Func.eval (weaken prf1 clos) h' scope a
           case res of
             End
               => pure (R h'' U (trans prf (trans prf1 prf2)))
             Ret v
               => pure (R h'' v (trans prf (trans prf1 prf2)))

    -- ### Annotations
    eval env heap (The _ expr)
      = eval env heap expr

  ||| Executing Statements
  namespace Stmts

    ||| Expressions return values, statements may return early.
    public export
    eval : {type : Ty}
        -> {store : List Ty}
        -> (env   : Env        stack store)
        -> (heap  : Heap             store)
        -> (expr  : Stmt types stack          type)
                 -> Ola (Result Return type store)

    -- ### Bindings
    eval env heap (Let _ expr rest)
      = do R h1 v prf1 <- eval env heap expr
           R h2 r prf2 <- Stmts.eval (v::weaken prf1 env) h1 rest
           pure (R h2 r (trans prf1 prf2))

    -- ### Sequencing
    eval env heap (Seq this notThis)
      = do R h1 U prf1 <- eval env heap this
           R h2 r prf2 <- eval (weaken prf1 env) h1 notThis
           pure (R h2 r (trans prf1 prf2))

    -- ### Conditionals
    eval env heap (Cond cond tt ff rest)

      = do R h' v prf <- eval env heap cond
           case v of
             (B False) => do R h'' v' prf' <- Stmts.eval (weaken prf env) h' ff
                             case v' of -- @TODO extract as it is a common pattern
                               Ret v
                                 => pure (R h'' v' (trans prf prf'))
                               End
                                 => do R h3 r prf3 <- Stmts.eval (weaken prf' (weaken prf env))
                                                                 h''
                                                                 rest
                                       pure (R h3 r (trans prf (trans prf' prf3)))


             (B True)  => do R h'' v' prf' <- Stmts.eval (weaken prf env) h' tt
                             case v' of
                               Ret v
                                 => pure (R h'' v' (trans prf prf'))
                               End
                                 => do R h3 r prf3 <- Stmts.eval (weaken prf' (weaken prf env))
                                                                 h''
                                                                 rest
                                       pure (R h3 r (trans prf (trans prf' prf3)))


    -- ### Matching
    eval env heap (Match expr left right rest)
      = do R h1 mres prf1 <- eval env heap expr
           case mres of
             Left v
               => do R h2 res prf2 <- Stmts.eval (v::weaken prf1 env)
                                                 h1
                                                 left
                     case res of
                       Ret v
                         => pure (R h2 res (trans prf1 prf2))
                       End
                         => do R h3 r prf3 <- Stmts.eval (weaken prf2 (weaken prf1 env))
                                                         h2
                                                         rest
                               pure (R h3 r (trans prf1 (trans prf2 prf3)))


             Right v
               => do R h2 res prf2 <- Stmts.eval (v::weaken prf1 env)
                                                 h1
                                                 right
                     case res of
                       Ret v
                         => pure (R h2 res (trans prf1 prf2))
                       End
                         => do R h3 r prf3 <- Stmts.eval (weaken prf2 (weaken prf1 env))
                                                         h2
                                                         rest
                               pure (R h3 r (trans prf1 (trans prf2 prf3)))

    -- ### Loop While
    eval env heap (While expr body rest)
           -- Evaluate the condition
      = do R h1 res prf1 <- eval env heap expr
           case res of
             (B False) -- Condition not satisfied, loop
               => do R h2 res prf2 <- Stmts.eval (weaken prf1 env) h1
                                                  body
                     case res of
                       Ret v -- Early return
                         => pure (R h2 res (trans prf1 prf2))
                       End -- Returned Unit
                         => do R h3 res prf3 <- assert_total
                                                  $ Stmts.eval (weaken prf2 (weaken prf1 env))
                                                               h2
                                                              (While expr body rest)
                               pure (R h3 res (trans prf1 (trans prf2 prf3)))

             (B True) -- Condition true, do rest
               => do R h2 res prf2 <- assert_total
                                         $ Stmts.eval (weaken prf1 env)
                                                      h1
                                                      rest
                     pure (R h2 res (trans prf1 prf2))

    -- ### Side effect
    eval env heap (Print this rest)
      = do R h' (S t) prf1 <- eval env heap this
           printLn t
           R h'' res prf2 <- eval (weaken prf1 env) h' rest
           pure $ R h'' res (trans prf1 prf2)


    -- ### Return the value
    eval env heap (Return expr)
      = do R h' res prf <- eval env heap expr
           pure (R h' (Ret res) prf)

    -- ### End of flow.
    eval env heap End
      = pure (R heap End (noChange _))

  namespace Func
    ||| Let's deal with functions separatly.
    public export
    eval : {store : List Ty}
        -> {a,ret : Ty}
        -> (env   : Env        stack store)
        -> (heap  : Heap             store)
        -> (func  : Func types stack          (FUNC a ret))
        -> (val   : Value store a)
                 -> Ola (Result Return ret store)
    -- non recursive
    eval env heap (Fun body) val
      = Stmts.eval (val::env) heap body

    -- [ NOTE ]
    -- This might not be the right way to do it...
    eval env heap (Rec body) val
      = do R h res prf <- Stmts.eval (val::env) heap body
           case res of
             Ret v -- we returned perhaps, 'early'
               => pure (R h res prf)
             End -- if not carry on.
               => do R h2 r p2 <- eval (weaken prf env)
                                   h
                                   (Rec body) (weaken prf val)
                     pure (R h2 r (trans prf p2))


namespace Progs
  ||| Need to resolve...
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
    = let Val a = (resolve env tmType) in Val (REF a)

  resolve env (TyHandle kind)
    = Val (HANDLE kind)

  resolve env (TyFunc tmA tmB)
    = let Val a = resolve env tmA
      in let Val b = resolve env tmB
      in Val (FUNC a b)

  resolve env (TyVar x)
    = (DList.lookup x env)

  ||| Run a programme.
  public export
  run : {type : Ty}
      -> {store : List Ty}
      -> (envT  : Env types)
      -> (env   : Env        stack store)
      -> (heap  : Heap             store)
      -> (expr  : Prog types stack          type)
               -> Ola (Result Return type store)

  -- Typedefs need resolving.
  run et env heap (DefType tyRef rest)
    = do let ty = resolve et tyRef
         R h1 res prf <- run (ty ::et)
                             env heap rest
         pure (R h1 res prf)

  -- Functions store their environment at time of definition.
  run et env heap (DefFunc sig func rest)
    = do R h1 res prf <- run et
                             (Clos func env :: env)
                             heap
                             rest
         pure (R h1 res prf)

  -- The main sh-bang
  run _ env heap (Main x)
    = Stmts.eval env heap x

||| Only run closed programmes.
export
exec : (prog : Programme)
            -> Ola ()

exec p
  = do ignore (run Nil Nil Nil p)
       pure ()

-- [ EOF ]
