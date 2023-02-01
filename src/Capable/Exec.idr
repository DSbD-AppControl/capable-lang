||| How to run Capable programmes.
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
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
module Capable.Exec

import Data.Maybe
import Data.Vect
import Data.String
import Data.List.Elem
import Data.List1.Elem
import Data.List.Quantifiers

import System.File

import Toolkit.Data.Vect.Extra
import Toolkit.Data.DList
import Toolkit.Data.DVect

import Capable.Core
import Capable.Terms
import Capable.Env
import Capable.Values

%default total
%hide type

-- # Rug Adaptations

throw : Running.Error -> Capable a
throw = (throw . Exec)

panic : (why : String) -> Capable a
panic = (throw . Panic)

error : (why : FileError) -> Capable a
error = (throw . Outside)

todo : Capable a -- i know...
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

    namespace NoChange
      export
      return : {store : List Ty.Base}
            -> (heap  : Heap store)
            -> (value : Value store type)
                     -> Capable (Result store type)
      return heap value = pure (Value heap value (noChange _))

    namespace Changed
      export
      return : {store,store' : List Ty.Base}
            -> (prf          : Subset store store')
            -> (res          : Result       store' type)
                            -> Capable (Result store   type)

      return prf (Value h val p)
        = pure (Value h val (trans prf p))

      export
      return2 : {store,store',store'' : List Ty.Base}
             -> (p1   : Subset store  store')
             -> (p2   : Subset        store' store'')
             -> (rest : Result store'' b)
                     -> Capable (Result store b)
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

  namespace Fields

    public export
    data Results : (store : List Ty.Base)
                -> (types : List (String,Ty.Base))
                         -> Type
      where
        Fields : {new   : List Ty.Base}
              -> (store : Heap  new)
              -> (args  : DList (String,Ty.Base) (Field new) types)
              -> (prf   : Subset  old new )
                       -> Results old types
  namespace ArgsV

    public export
    data Results : (store : List Ty.Base)
                -> (types : Vect n Ty.Base)
                         -> Type
      where
        Args : {new   : List Ty.Base}
            -> (store : Heap  new)
            -> (args  : DVect Ty.Base (Value new) n types)
            -> (prf   : Subset  old new )
                     -> Results old types

||| An API to support expressions that interact with the heap.
namespace Heap

  export
  insert : {store : List Ty.Base}
        -> {type  : Ty.Base}
        -> (value : Value store type)
        -> (heap  : Heap  store)
                 -> Capable (Expr.Result store (REF type))
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
                -> Capable (Expr.Result store type)
  fetch loc heap
    = let val = Heap.lookup loc heap
      in return heap val


  export
  mutate : {store : List Ty.Base}
        -> (loc   : IsVar store type)
        -> (heap  : Heap store)
        -> (val   : Val type store)
                 -> Capable (Expr.Result store UNIT)

  mutate loc heap val
    = let new_heap = Heap.replace loc val heap
      in return new_heap U


debase : FileError -> Int
debase (GenericFileError i) =  i - 5
debase FileReadError = 0
debase FileWriteError = 1
debase FileNotFound = 2
debase PermissionDenied = 3
debase FileExists = 4

-- # Executing stuff, finally...

mutual

  namespace Fields
    export
    eval : {store : List Ty.Base}
        -> {as    : List (String,Base)}
        -> (env   : Env stack_g stack_l store)
        -> (heap  : Heap store)
        -> (args  : DList (String, Ty.Base) (Field rs tys gs stack_g stack_l) as)
                 -> Capable (Fields.Results store as)
    eval env heap []
      = pure (Fields heap
                     Nil
                     (noChange _))

    eval env heap ((F s x) :: xs)
      = do Value  h v  p  <- eval env heap x
           Fields h vs ps <- eval (weaken p env) h xs
           pure (Fields h
                      (F s (weaken ps v)::vs)
                      (trans p ps))

  namespace Args
    export
    eval : {as,store : List Ty.Base}
        -> (env   : Env stack_g stack_l store)
        -> (heap  : Heap store)
        -> (args  : DList Ty.Base (Expr rs tys gs stack_g stack_l) as)
                 -> Capable (Args.Results store as)
    eval env heap []
      = pure (Args heap
                   Nil
                   (noChange _))

    eval env heap (x :: xs)
      = do Value h v  p  <- eval env heap x
           Args  h vs ps <- eval (weaken p env) h xs
           pure (Args h
                      ((weaken ps v)::vs)
                      (trans p ps))

  namespace ArgsV
    export
    eval : {as    : Vect n Ty.Base}
        -> {store : List Ty.Base}
        -> (env   : Env stack_g stack_l store)
        -> (heap  : Heap store)
        -> (args  : DVect Ty.Base (Expr rs tys gs stack_g stack_l) n as)
                 -> Capable (Results store as)
    eval env heap []
      = pure (Args heap
                   Nil
                   (noChange _))

    eval env heap (x :: xs)
      = do Value h v  p  <- eval env heap x
           Args  h vs ps <- eval (weaken p env) h xs
           pure (Args h
                      ((weaken ps v)::vs)
                      (trans p ps))
  namespace Builtins
    ||| Executing builtins
    export
    eval : {0 inputs : List Base}
        -> {  store  : List Base}
        -> (  heap   : Heap store)
        -> (  desc   : Builtin inputs ret)
        -> (  args   : DList Ty.Base (Value store) inputs)
                    -> Capable (Expr.Result store ret)

    -- ## Constants
    eval heap U     [] = return heap U
    eval heap (C c) [] = return heap (C c)
    eval heap (S s) [] = return heap (S s)
    eval heap (I i) [] = return heap (I i)
    eval heap (B b) [] = return heap (B b)

    -- can be better with a view.

    -- ## Char Ops
    eval heap (CharOp Ord) [C c]
      = return heap (I (ord c))

    eval heap (CharOp Chr) [I i]
      = return heap (C (chr (cast i)))

    eval heap (CharOp Singleton) [C c]
      = return heap (S (singleton c))


    -- ## String Ops
    eval heap (StrOp Length) [S s]
      = return heap (I (cast (length s)))

    eval heap (StrOp Cons) [C c, S s]
      = return heap (S (singleton c ++ s))

    eval heap (StrOp Slice) [I st, I ed, S s]
      = return heap (S (strSubstr st ed s))

    eval heap (ToString CC) [C c] = return heap (S (singleton c))
    eval heap (ToString CS) [S s] = return heap (S s)
    eval heap (ToString CI) [I i] = return heap (S (show i))
    eval heap (ToString CB) [B b] = return heap (S (show b))

    -- ## Maths
    eval heap (BinOpInt ADD) [I a, I b] = return heap (I $ (+) a b)
    eval heap (BinOpInt SUB) [I a, I b] = return heap (I $ (-) a b)
    eval heap (BinOpInt DIV) [I a, I b] = return heap (I $ div a b)
    eval heap (BinOpInt MUL) [I a, I b] = return heap (I $ (*) a b)

    -- ## Binary
    eval heap (BinOpBool AND) [B a, B b] = return heap (B $ (&&) a b)
    eval heap (BinOpBool OR)  [B a, B b] = return heap (B $ (||) a b)

    eval heap Not [B b]
      = return heap (B (not b))

    -- can be better with a view.
    eval heap (Cmp CC LT)  [C a, C b] = return heap (B $ (<)  a b)
    eval heap (Cmp CC LTE) [C a, C b] = return heap (B $ (<=) a b)
    eval heap (Cmp CC EQ)  [C a, C b] = return heap (B $ (==) a b)
    eval heap (Cmp CC GT)  [C a, C b] = return heap (B $ (>)  a b)
    eval heap (Cmp CC GTE) [C a, C b] = return heap (B $ (>=) a b)

    eval heap (Cmp CS LT)  [S a, S b] = return heap (B $ (<)  a b)
    eval heap (Cmp CS LTE) [S a, S b] = return heap (B $ (<)  a b)
    eval heap (Cmp CS EQ)  [S a, S b] = return heap (B $ (==) a b)
    eval heap (Cmp CS GT)  [S a, S b] = return heap (B $ (>)  a b)
    eval heap (Cmp CS GTE) [S a, S b] = return heap (B $ (>=) a b)

    eval heap (Cmp CI LT)  [I a, I b] = return heap (B $ (<)  a b)
    eval heap (Cmp CI LTE) [I a, I b] = return heap (B $ (<=) a b)
    eval heap (Cmp CI EQ)  [I a, I b] = return heap (B $ (==) a b)
    eval heap (Cmp CI GT)  [I a, I b] = return heap (B $ (>)  a b)
    eval heap (Cmp CI GTE) [I a, I b] = return heap (B $ (>=) a b)

    eval heap (Cmp CB LT)  [B a, B b] = return heap (B $ (<)  a b)
    eval heap (Cmp CB LTE) [B a, B b] = return heap (B $ (<=) a b)
    eval heap (Cmp CB EQ)  [B a, B b] = return heap (B $ (==) a b)
    eval heap (Cmp CB GT)  [B a, B b] = return heap (B $ (>)  a b)
    eval heap (Cmp CB GTE) [B a, B b] = return heap (B $ (>=) a b)

    -- ## Memory
    eval heap Fetch [(Address adr)]
      = fetch adr heap

    eval heap Alloc [this]
      = insert this heap

    eval heap Mutate [Address adr, val]
      = mutate adr heap val


    -- ## Process
    eval heap (Open what m) [(S fname)]
      = either (\err => return heap (left  (HANDLE what) (I (debase err))))
               (\fh  => return heap (right (HANDLE what) (H what fh)))
               (!(getHandle what))


      where getHandle : (k : HandleKind)
                     -> Capable (Either FileError File)
            getHandle FILE    = embed (openFile fname m)
            getHandle PROCESS = embed (popen    fname m)

    eval heap ReadLn [H k fh]
      = either (\err => return heap (left  STR (I (debase err))))
               (\str => return heap (right STR (S str)))
               (!(embed $ fGetLine fh))

    eval heap WriteLn [H k fh, (S str)]
      = either (\err => return heap (left  UNIT (I (debase err))))
               (\str => return heap (right UNIT U))
               (!(embed $ fPutStrLn fh str))

    eval heap Close [H k fh]
      = case k of
           FILE
             => do embed (closeFile fh)
                   return heap U
           PROCESS
             => do v <- embed (pclose fh)
                   return heap U

    -- ## Misc
    eval heap Print [S s]
      = do putStr s
           return heap U

  ||| Executing Expressions
  namespace Exprs
    %inline
    when : {type : Ty.Base}
        -> (env  : Env stack_g stack_l store)
        -> (cond : Expr.Result store BOOL)
        -> (tt   : Expr roles types gs stack_g stack_l type)
        -> (ff   : Expr roles types gs stack_g stack_l type)
                -> Capable (Expr.Result store type)

    when env (Value h (B False) prf) _ ff
      = do Value hf vf prfF <- Exprs.eval (weaken prf env) h ff
           pure (Value hf vf (trans prf prfF))

    when env (Value h (B True) prf) tt _
      = do Value hf vf prfF <- Exprs.eval (weaken prf env) h tt
           pure (Value hf vf (trans prf prfF))


    public export
    eval : {type  : Ty.Base}
        -> {store : List Ty.Base}
        -> (env   : Env stack_g stack_l store)
        -> (heap  : Heap store)
        -> (expr  : Expr roles types globals stack_g stack_l type)
                 -> Capable (Expr.Result store type)
    -- ### Holes
    eval env heap (Hole s)
      = panic "Encountered a hole: \{show s}"

    -- ### Variables
--    eval env heap (VarG x)
--      = return heap
--               (lookup_g x env)

    eval env heap (Var x)
      = return heap
               (lookup_l x env)

    -- ### Bindings
    eval env heap (Let _ expr rest)
      = do Value h v p <- eval env heap expr
           res <- eval (extend_l v $ weaken p env) h rest
           return p res

    eval env heap (Split t rest)
      = do Value h (Tuple vs) prf <- eval env heap t
           res <- eval (extend_ls vs $ weaken prf env) h rest
           return prf res

    -- ## Sequences
    eval env heap (Seq this that)
      = do Value h v p <- eval env heap this
           res <- eval (weaken p env) h that
           return p res

    -- ### Builtins
    eval env heap (Builtin desc args)
      = do Args h args prf1 <- Args.eval env heap args
           Value h' v prf2 <- Builtins.eval h desc args
           pure (Value h' v (trans prf1 prf2))

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
        = do Value h'  (I idx) p1 <- eval env heap idx
             Value h'' arr     p2 <- eval (weaken p1 env) h' array
             let Val s = size arr

             if idx < 0
              then throw (OOB idx s)
              else maybe (throw (OOB idx s))
                         (\idx => pure (Value h'' (index idx arr) (trans p1 p2)))
                         (natToFin (cast idx) s)

    -- ### Data Structures

    -- #### Products
    eval env heap (Tuple as)
      = do Args heap as prf <- ArgsV.eval env heap as
           pure (Value heap (Tuple as) prf)

    eval env heap (Set as idx v)
      = do Value heap (Tuple vs) prf  <- eval env heap as
           Value heap v'         prf' <- eval (weaken prf env) heap v
           pure (Value heap ((Tuple (update (weaken prf' vs) idx v'))) (trans prf prf'))

    eval env heap (Get as idx)
      = do Value heap (Tuple vs) prf <- eval env heap as
           let vs' = index vs idx
           pure $ Value heap vs'
                             prf

    -- ### Records
    eval env heap (Record fs)
      = do Fields heap fs prf <- eval env heap fs
           pure (Value heap (Record fs) prf)

    eval env heap (SetR as idx v)
      = do Value heap (Record vs) prf  <- eval env heap as
           Value heap v'         prf' <- eval (weaken prf env) heap v
           pure (Value heap
                       ((Record (replace idx
                                         (F _ v')
                                         (weaken prf' vs) )))
                       (trans prf prf'))

    eval env heap (GetR as idx)
      = do Value heap (Record vs) prf <- eval env heap as
           let (F _ vs') = lookup idx vs
           pure $ Value heap vs'
                             prf

    -- ### Sums
    eval env heap (Tag s val pos)
      = do Value heap v prf <- eval env heap val
           pure (Value heap (Tag s pos v) prf)

    -- ### Matching
    eval env heap (Match expr cases)
      = do Value heap (Tag s pos v) prf <- eval env heap expr
           let kase = lookup pos cases
           Value heap v prf' <- eval (extend_l v (weaken prf env)) heap kase
           pure (Value heap v (trans prf prf'))

      where
        lookup : {s : String}
              -> {ret : Base}
              -> (idx : Elem (s,x) xs)
              -> (ps  : DList (String,Base)
                              (Case roles types globals stack_g stack_l ret)
                              xs)
                     -> Expr roles types globals stack_g (x::stack_l) ret
        lookup Here (C s elem :: rest) = elem
        lookup (There y) (elem :: rest) = lookup y rest

    -- ### Annotations

    eval env heap (The _ expr)
      = eval env heap expr


    eval env heap (Loop body expr)
      = do Value h' res  p  <- eval env heap body
           Value h  cres p2 <- eval (weaken p env) h' expr
           case cres of
             B True -- Loop
               => do r <- eval (weaken p2 (weaken p env))
                               h
                               (Loop body expr)
                     return2 p p2 r

             B False -- Return
               => pure (Value h (weaken p2 res) (trans p p2))

    -- ### Function Calls

    eval env heap (Call f xs)
           -- Fetch closure
      = do let (ClosFunc scope clos) = lookup_g f env

           -- Evaluate args
           Args h args p1 <- Args.eval env heap xs

           -- Call function
           Value h v p2   <- Func.eval clos h scope args

           pure (Value h
                       v
                       (trans p1 p2))

    eval env heap (Run s argsc argsv) = panic "Not Yet Implemented"


  namespace Sesh
    ||| Let's deal with functions separatly.
    public export
    eval : {store : List Ty.Base}
        -> {as    : List Ty.Base}
        -> {ret   : Ty.Base}
        -> (env   : DList Ty.Method (Closure) stack_g)
        -> (heap  : Heap store)
        -> (func  : Session roles types globals stack_g (SESH w l as ret))
        -> (vals  : DList Ty.Base (Value store) as)
                 -> Capable (Expr.Result store ret)
    eval env heap func vals = panic "Not Yet Implemented"

--    eval env_g heap (Sesh body) args
--      = ?aas -- eval (MkEnv env_g args) heap body

  namespace Func
    ||| Let's deal with functions separatly.
    public export
    eval : {store : List Ty.Base}
        -> {as    : List Ty.Base}
        -> {ret : Ty.Base}
        -> (env   : DList Ty.Method (Closure) stack_g)
        -> (heap  : Heap store)
        -> (func  : Func roles types globals stack_g (FUNC as ret))
        -> (vals  : DList Ty.Base (Value store) as)
                 -> Capable (Expr.Result store ret)
    eval env_g heap (Fun body) args
      = eval (MkEnv env_g args) heap body


||| Run a programme.
public export
run : {type : Ty.Base}
    -> {store : List Ty.Base}
    -> (envR  : Env roles)
    -> (envT  : Env types)
    -> (env   : DList Ty.Method (Closure) stack)
    -> (heap  : Heap store)
    -> (expr  : Prog roles types globals stack type)
             -> Capable (Expr.Result store type)

run er et env heap (DefProt s scope)
  = run er et env heap scope

run er et env heap (DefRole rest)
  = run (Val MkRole::er)
        et
        env
        heap
        rest


-- Typedefs need resolving.
run er et env heap (DefType tyRef rest)
  = run er
        (Val _::et)
        env
        heap
        rest


-- Functions store their environment at time of definition.
run er et env heap (DefFunc func rest)
  = run er
        et
        (ClosFunc func env :: env)
        heap
        rest

run er et env heap (DefSesh _ _ _ s rest)
  = run er
        et
        (ClosSesh s env :: env)
        heap
        rest

-- The main sh-bang
run _ _ env heap (Main x)
  = eval env heap x Nil

||| Only run closed programmes.
export
exec : (prog : Program)
            -> Capable ()

exec p
  = do ignore (run Nil Nil Nil Nil p)
       pure ()

-- [ EOF ]
