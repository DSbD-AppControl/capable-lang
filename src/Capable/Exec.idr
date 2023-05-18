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
import System.Escape
import Toolkit.Data.Vect.Extra
import Toolkit.Data.DList
import Toolkit.Data.DVect

import Capable.Core
import Capable.Terms

import Capable.Values
import Capable.Values.Marshall

import Capable.Exec.Env
import Capable.Exec.Common
import Capable.Exec.Results
import Capable.Exec.Heap
import Capable.Exec.IPC
import Capable.Exec.Offers


%default total
%hide type



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
        -> (tt   : Expr rs types gs stack_g stack_l type)
        -> (ff   : Expr rs types gs stack_g stack_l type)
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
        -> (expr  : Expr rs types globals stack_g stack_l type)
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
      = do let (ClosFunc scope clos _) = lookup_g f env

           -- Evaluate args
           Args h args p1 <- Args.eval env heap xs

           -- Call function
           Value h v p2   <- Func.eval clos h scope args

           pure (Value h
                       v
                       (trans p1 p2))

    eval env heap (Run s argsc _ argsv)
      = do let (ClosSesh rs scope clos) = lookup_g s env

           -- Evaluate args
           Args h args p1 <- Args.eval env heap argsv

           Value h ass p2 <- assigns (weaken p1 env)
--                                     rs
                                     h argsc
           cs <- init rs ass

           cs <- startAll cs

           Value h cs v p3 <- Session.eval clos h cs scope (weaken p2 args)

           cs <- closeAll cs

           pure (Value h v
                         (trans p1 (trans p2 p3)))



    assigns : {store : List Ty.Base}
           -> (env   : Env stack_g stack_l store)

--           -> (er    : Env rs)
           -> (heap  : Heap store)
           -> (expr  : Assignments rs roles types globals stack_g stack_l proto princs)
                    -> Capable (Assigns.Result store rs princs)

    assigns env heap Empty
      = pure (Value heap Empty (noChange _))

    assigns env heap (KV whom val kvs)
      = do Value heap v prf <- eval env heap val
           Value heap kvs prf1 <- assigns (weaken prf env) heap kvs

           pure (Value heap (KV whom (weaken prf1 v) kvs)
                       (trans prf prf1))

  namespace Session
    public export
    eval : {store : List Ty.Base}
        -> {as    : List Ty.Base}
        -> {ret   : Ty.Base}
        -> {ctzt  : Context Role rz}
        -> (env   : DList Ty.Method (Closure) stack_g)
        -> (heap  : Heap store)
        -> (cs    : Channels rz)
        -> (func  : Session roles types globals stack_g (SESH ctzt w l as ret))
        -> (vals  : DList Ty.Base (Value store) as)
                 -> Capable (Session.Exprs.Result rz store ret)
    eval env_g heap cs (Sesh body) vals
      = Session.Exprs.eval (MkEnv env_g vals) heap Nil cs body


    namespace Exprs

      public export
      eval : {store : List Ty.Base}
          -> {ret   : Ty.Base}
          -> (env   : Env stack_g stack_l store)
          -> (heap  : Heap store)
          -> (rvars : Env rs roles types globals stack_g stack_r ret)
          -> (chans : Channels rs)
          -> (sesh  : Sessions.Expr rs roles types globals stack_g stack_l stack_r whom l ret)
                   -> Capable (Session.Exprs.Result rs store ret)

      eval env heap rvars cs (Hole s)
        = panic "Encountered a hole: \{show s}"


      eval env heap rvars cs (Split t rest)
        = do Value h (Tuple vs) prf <- Exprs.eval env heap t
             Value h cs' v prf' <- eval (extend_ls vs $ weaken prf env) h rvars cs rest
             pure (Value h cs' v (trans prf prf'))

      -- [ NOTE ] Compute the (unsafe) expression and then carry on...
      eval env heap rvars cs (Seq x y)
        = do Value h U prf <- Exprs.eval env heap x
             Value h cs' v prf' <- eval (weaken prf env) h rvars cs y
             pure (Value h cs' v (trans prf prf'))

      -- [ NOTE ] Local binders...
      eval env heap rvars cs (Let _ expr rest)
        = do Value h v prf0 <- Exprs.eval env heap expr
             let env = extend_l v $ weaken prf0 env
             Value h cs v prf1 <- eval env h rvars cs rest
             pure (Value h cs v (trans prf0 prf1))

      -- [ NOTE ] Push a closure onto the stack...
      eval env@(MkEnv eg el) heap rvars cs (LetRec x)
        = do let c = SS x el rvars :: rvars
             Value h cs v prf0 <- Exprs.eval env heap c cs x
             pure (Value h cs v prf0)

      -- [ NOTE ] Pop a closure and resume...
      eval (MkEnv env_g _) heap rvars cs (Call loc)
        = do let SS expr env_l env_rs = read loc rvars

             -- [ NOTE ] nothing to see carry-on
             --
             -- this is an absurd hack.
             case isSubset heap env_l of
               No _ => panic "Shouldn't happen..."
               Yes prf => do let env = weaken prf $ (MkEnv env_g env_l)
                             Value h cs v prf <- Exprs.eval env heap env_rs cs (LetRec expr)
                             pure (Value h cs v prf)

      -- [ NOTE ]
      eval env heap rvars cs (Cond test tt ff)
        = do Value h (B b) prf0 <- Exprs.eval env heap test
             if b
               then do Value h cs v prf1 <- eval (weaken prf0 env) h rvars cs tt
                       pure (Value h cs v (trans prf0 prf1))

               else do Value h cs v prf1 <- eval (weaken prf0 env) h rvars cs ff
                       pure (Value h cs v (trans prf0 prf1))


      -- [ NOTE ] The end of a communication session, must return
      -- something...
      eval env heap rvars cs (End x)
        = do Value h x prf <- Exprs.eval env heap x
             pure (Value h cs x prf)

      -- [ NOTE ] The end of a *failed* communication session, must return something...
      eval env heap rvars cs (Crash x)
        = do Value h v prf0 <- Exprs.eval env heap x
             pure (Value h cs v prf0)

      -- [ NOTE ]
      --
      -- Try to:
      --
      -- 1. Read from the wire on the prescribed channel
      -- 2. Perform Type-directed unmarshalling
      --
      -- If this fails then crash
      -- Else index into offers and continue
      eval env heap rvars cs (Read from prf offers onErr)
          = tryCatchFinally
                (do str <- recvOn from cs
                    unmarshall prf str)

                (\err => do Value h cs v p <- Exprs.eval env
                                                   heap
                                                   rvars
                                                   cs
                                                   onErr
                            pure (Value h cs v p))
                (\(Tag s idx val)
                    => do let (_ ** O _ body) = getIndex idx offers
                          let e' = extend_l (strengthen heap val Empty) env
                          Value h cs v p <- Exprs.eval e'
                                                   heap
                                                   rvars
                                                   cs
                                                   body
                          pure (Value h cs v p))


      -- [ NOTE ]
      -- Marshalling is a pure operation.
      --
      -- 1. marshall the data
      -- 2. Get the channel.
      -- 3. ship
      -- 4. if crash then continue else continue
      --
      eval env heap rvars cs (Send toWhom label payload marsh rest onErr)
        = do Value h v prf <- Exprs.eval env heap payload
             msg <- marshall (F label marsh) v
             tryCatchFinally
               (sendOn (show msg) toWhom cs)
               (\err => do Value h cs v p <- Exprs.eval (weaken prf env)
                                                  h
                                                  rvars
                                                  cs
                                                  onErr
                           pure (Value h cs v (trans prf p)))
               (\val => do Value h cs v p <- Exprs.eval (weaken prf env)
                                                        h
                                                        rvars
                                                        cs
                                                        rest
                           pure (Value h cs v (trans prf p)))

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
        (ClosFunc func env er :: env)
        heap
        rest

run er et env heap (DefSesh s rest)
  = run er
        et
        (ClosSesh _ s env :: env)
        heap
        rest

-- The main sh-bang
run er _ env heap (Main x)
  = eval env heap x Nil


||| Only run closed programmes.
export
exec : (prog : Program)
            -> Capable ()

exec p
  = do ignore (run Nil Nil Nil Nil p)
       pure ()

-- [ EOF ]
