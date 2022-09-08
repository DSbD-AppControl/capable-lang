||| Example programmes.
|||
||| Module    : Example.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
module Example

import Ola.Core
import Ola.Terms
import Ola.Exec

||| An example programme.
|||
||| Concrete Syntax:
|||
||| ```
||| type foo = String;
|||
||| fn hWorld () : String
||| {
|||   return "Hello World"
||| }
|||
||| fn main()
||| {
|||   let String s = hWorld();
|||   print(s);
|||   return ()
||| }
||| ```
public export
example : Program
example
  = DefType TyStr
  $ DefFunc (TyFunc Nil (TyVar Here))
            (Fun End
                 (S "Hello World")
            )
  $ Main
  $ Fun (Let TyStr (Call (Var Here) Nil)
        $ Print (Var Here) $ End)
        $ U

{-
||| An example programme.
|||
||| Concrete Syntax:
|||
||| ```
||| fn extract (x : Union String Int) : String
||| {
|||   return (match x { Left(s) => s
|||                   | Right(i) => "Hello"
|||                   })
||| }
|||
||| fn main()
||| {
|||   let (Union String Int) foo = Left("AA");
|||   print(extract(foo));
|||   return ()
||| }
||| ```
public export
example1 : Program
example1
  = DefFunc (TyFunc [TyUnion TyStr TyInt]
                    TyStr)
            (Fun Empty
                 (Match (Var Here)
                                 (Var Here)
                                 (S "Hello"))
            )
  $ Main
  $ Block
  $ Cons (Let (TyUnion TyStr TyInt)
              (Left (S "AA")))
  $ Cons (Print (Call (Var (There Here))
                      [Var Here]))
  $ Cons (Return U)
  $ Empty
-}

public export
example2 : Prog Nil Nil UNIT
example2
  = Main
  $ Fun
    (Let (TyRef TyStr)
         (Alloc (S "HelloWorld"))
  $ Print (S "Example 2")
  $ Print (Fetch $ Var Here)
  $ (Cond (B True)
          (Mutate (Var (Here)) (S "Goodbye World")   $ End)
          (Mutate (Var (Here)) (S "Tot Ziens World") $ End)
    )
  $ Print (Fetch $ Var Here)
  $ End)
  U

{-
public export
example3 : Prog Nil Nil UNIT
example3
  = DefFunc (TyFunc [TyUnion TyStr TyInt]
                    TyStr)
            (Fun (Cons (Let (TyRef TyStr)
                             (Alloc (S "HelloWorld")))
                 $ Cons (Print (Fetch $ Var Here))
                 $ Cons (Cond (B True)
                              (Run (Mutate (Var (Here)) (S "Goodbye World")))
                              (Run (Mutate (Var (Here)) (S "Tot Ziens World")))
                        )
                 $ Cons (Print (Fetch $ Var Here))
                 $ Empty)
                 (Match (Var (There Here))
                             (Var Here)
                             (S "Hello"))
            )
  $ Main
  $ Block
  $ Cons (Let (TyUnion TyStr TyInt)
              (Left (S "AA")))
  $ Cons (Print (Call (Var (There Here))
                      [Var Here]))
  $ Cons (Return U)
  $ Empty

-}


public export
example4 : Program
example4
  = DefFunc (TyFunc [TyBool]
                    TyStr)
            (Fun (Print (S "Start of Function")
                 $ Let (TyRef TyStr)
                      (Alloc (S "example 4"))
                 $ Print (Fetch $ Var Here)
                 $ Cond (Var (There Here))
                        (Return (S "Tot Ziens"))
                        (Mutate (Var (Here)) (S "World") $ End)
                 $ Print (Fetch $ Var Here)
                 $ Print (S "End of Function")
                 $ End)
                 (Fetch $ Var Here)
            )
  $ Main
  $ Fun ( Print (S "Example 4")
        $ Print (Call (Var Here) [B True])
        $ Print (Call (Var Here) [B False])
        $ End)
        U

-- [ EOF ]
