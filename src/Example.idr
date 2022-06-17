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
example : Prog Nil Nil UNIT
example
  = DefType TyStr
  $ DefFunc (TyFunc TyUnit (TyVar Here))
            (Fun (Return (S "Hello World")
            ))
  $ Main
  $ Let TyStr
        (Call (Var Here) U)
  $ Print (Var Here)
  $ Return U


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
example1 : Prog Nil Nil UNIT
example1
  = DefFunc (TyFunc (TyUnion TyStr TyInt)
                    TyStr)
            (Fun (Return $ Match (Var Here)
                                 (Var Here)
                                 (S "Hello")
            ))
  $ Main
  $ Let (TyUnion TyStr TyInt)
        (Left (S "AA"))
  $ Print (Call (Var (There Here))
                (Var Here))
  $ Return U

public export
example2 : Prog Nil Nil UNIT
example2
  = Main
  $ Let (TyRef TyStr)
        (Alloc (S "HelloWorld"))
  $ Print (Fetch $ Var Here)
  $ Seq (Mutate (Var Here)
                (S "Goodbye World"))
  $ Print (Fetch $ Var Here)
  $ Return U


-- [ EOF ]
