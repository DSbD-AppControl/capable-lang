||| Rust Codegen via the elaborated AST
|||
|||
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Capable.Codegen.Rust

import Data.Maybe
import Data.Vect
import Data.String
import Data.List.Elem
import Data.List1.Elem
import Data.List.Quantifiers
import Data.Vect.Quantifiers

import System.File
import System.Escape

import Text.PrettyPrint.Prettyprinter
import Text.PrettyPrint.Prettyprinter.Render.String


import Toolkit.Data.Vect.Extra
import Toolkit.Data.DList
import Toolkit.Data.DVect

import Capable.Core

import Capable.Types

import Capable.Raw.AST
import Capable.Raw.Role
import Capable.Raw.Protocols
import Capable.Raw.Types
import Capable.Raw.DTypes
import Capable.Raw.Exprs
import Capable.Raw.Funcs
import Capable.Raw.Sessions
import Capable.Raw.Progs

%default total

binderValue : String -> Doc ()
binderValue
  = pretty

binderType : String -> Doc ()
binderType
  = pretty

refValue : Ref -> Doc ()
refValue = binderValue . get

refType : Ref -> Doc ()
refType = binderType . get


||| Map Capable Types to Rusty Types
|||
|||
type : Ty t -> Doc ()
type (TyVar r prf)
  = refType r

type (TyChar fc)
  = pretty "chr"

type (TyStr fc)
  = pretty "String"

type (TyInt fc)
  = pretty "usize"

type (TyBool fc)
  = pretty "bool"

type (TyUnit fc)
  = pretty "()"

type (TyList fc ty)
  = hcat
    [ pretty "Vec"
    , angles (type ty)
    ]

type (TyVector fc n ty)
  = brackets
  $ hcat
    [ type ty
    , semi
    , pretty n
    ]

type (TyTuple fc prf fs)
  = tupled
  $ pretty fs

  where pretty : Types.Args fs'
              -> List (Doc ())
        pretty []
          = []
        pretty (ty :: rest)
          = type ty :: pretty rest

type (TyRef fc ty)
  = hsep
    [ pretty "&mut"
    , type ty
    ]

type (TyHandle fc FILE)
  = pretty "File"

type (TyHandle fc PROCESS)
  = pretty "Child"


kvs : (forall t . Ty t -> Doc ()) -> Named.Args fs -> List (Doc ())
kvs _ []
  = []

kvs ann (Add fc s ty rest)
  = (group $ hsep [binderType s, colon, ann ty])  :: kvs ann rest

typeFields : List (Doc ()) -> Doc ()
typeFields
  = group . encloseSep (flatAlt ("{ ") ("{"))
                       (flatAlt (" }") ("}"))
                       ("; ")

datatype : String -> DTy d -> Doc ()
datatype n (TyData fc STRUCT prf fs)
  = group
  $ hsep
    [ pretty "struct"
    , binderType n
    , typeFields $ assert_total $ kvs type fs]

datatype n (TyData fc UNION prf fs)
  = group
  $ hsep
    [ pretty "enum"
    , binderType n
    , typeFields $ assert_total $ kvs type fs
    ]

farg : Arg a -> Doc ()
farg (A fc n ty)
  = hsep
  [ binderValue n
  , colon
  , assert_total $ type ty
  ]


fargs : Vect.Quantifiers.All.All Arg az -> List (Doc ())
fargs []
  = Nil

fargs (x :: y)
  = farg x :: fargs y

uno : String
   -> Doc ()
   -> Doc ()
uno f a
  = group
  $ hcat
    [ pretty f
    , parens a
    ]

duo : String
   -> Doc ()
   -> Doc ()
   -> Doc ()
duo f a b
  = group
  $ hcat
    [ pretty f
    , tupled [a,b]
    ]

tri : String
   -> Doc ()
   -> Doc ()
   -> Doc ()
   -> Doc ()
tri f a b c
  = group
  $ hcat
    [ pretty f
    , tupled [a, b, c]
    ]

stored : Stored -> Doc ()
stored HEAP
  = hsep
    [ "let"
    , "&mut"
    ]

stored STACK
  = pretty "let"

{-
prettyMode : Mode -> Doc ()
prettyMode Read              = "r"
prettyMode WriteTruncate     = "w"
prettyMode Append            = "a"
prettyMode ReadWrite         = "r+"
prettyMode ReadWriteTruncate = "w+"
prettyMode ReadAppend        = "a+"

handlekind : HandleKind -> Doc ()
handlekind FILE = keyword "fopen"
handlekind PROCESS = keyword "popen"

structs : List (Doc ()) -> Doc ()
structs
  = group . encloseSep (flatAlt ("{ ") ("{"))
                       (flatAlt (" }") ("}"))
                       (", ")

-}

cond : Doc () -> Doc () -> Doc () -> Doc ()
cond c t f
  = vsep
    [ hsep [ pretty "if", c]
    , lbrace
    , indent 2 t
    , hsep [ rbrace , pretty "else" ]
    , lbrace
    , indent 2 f
    , rbrace
    ]

expr : Raw.Exprs.Expr b -> Doc ()
expr _ = pretty "// TODO"
{-
expr (Hole ref prf)
  = hsep
    [ pretty "// "
    , refValue ref
    ]

expr (Var r prf)
  = refValue r

expr (LetTy fc s st ty val scope)
  = vsep
    [ group
      $ hsep
        [ stored st
        , binderValue s
        , colon
        , type ty
        , equals
        , expr val
        , semi
        ]
    , expr scope
    ]
expr (Let fc s st val scope)
  = vsep
    [ group
      $ hsep
        [ stored st
        , binderValue s
        , equals
        , expr val
        , semi
        ]
    , expr scope
    ]

expr (Split fc ss val scope)
  = vsep
  [ hsep
    [ pretty "match"
    , expr val
    ]
  , lbrace
  , align
    $ indent 2
    $ hsep
      [ tupled $ map pretty ss
      , pretty "=>"
      , expr scope
      ]
  , rbrace
  ]

expr (Const fc UNIT v)
  = pretty "()"

expr (Const fc CHAR v)
  = squotes $ v' v

  where v' : Char -> Doc ()
        v' c = if isNL c then pretty "\\n" else pretty c

expr (Const fc STR v)
  = dquotes $ pretty v

expr (Const fc INT v)
  = pretty v

expr (Const fc BOOL v)
  = pretty v

expr (OpBin fc WRITE l r) = duo "write" (expr l) (expr r)
expr (OpBin fc AND l r)     = duo "and" (expr l) (expr r)
expr (OpBin fc OR l r)      = duo "or" (expr l) (expr r)
expr (OpBin fc LT l r)      = duo "lt" (expr l) (expr r)
expr (OpBin fc LTE l r)     = duo "lte" (expr l) (expr r)
expr (OpBin fc EQ l r)      = duo "eq" (expr l) (expr r)
expr (OpBin fc GT l r)      = duo "gt" (expr l) (expr r)
expr (OpBin fc GTE l r)     = duo "gte" (expr l) (expr r)
expr (OpBin fc ADD l r)     = duo "add" (expr l) (expr r)
expr (OpBin fc SUB l r)     = duo "sub" (expr l) (expr r)
expr (OpBin fc MUL l r)     = duo "mul" (expr l) (expr r)
expr (OpBin fc DIV l r)     = duo "div" (expr l) (expr r)
expr (OpBin fc STRCONS l r) = duo "strCons" (expr l) (expr r)
expr (OpBin fc MUT l r)     = duo "mut" (expr l) (expr r)

expr (OpUn fc PRINT o)      = uno "print" (expr o)
expr (OpUn fc FETCH o)      = hcat [pretty "&", expr o]
expr (OpUn fc READ o)       = uno "read" (expr o)
expr (OpUn fc CLOSE o)      = uno "close" (expr o)
expr (OpUn fc NOT o)        = uno "not" (expr o)
expr (OpUn fc SIZE o)       = uno "size" (expr o)
expr (OpUn fc ORD o)        = uno "ord" (expr o)
expr (OpUn fc CHR o)        = uno "chr" (expr o)
expr (OpUn fc STRO o)       = uno "string" (expr o)
expr (OpUn fc TOSTR o)      = uno "toString" (expr o)
expr (OpUn fc POPEN2 o)      = uno "popen2" (expr o)
expr (OpUn fc (OPEN x y) o)
  = group
  $ pretty "TODO"
  --(handlekind x <+> tupled [prettyMode y, expr o])

expr (MkList fc _ xs)
  = list (args xs)
  where args : Vect.Quantifiers.All.All Exprs.Expr as -> List (Doc ())
        args [] = []
        args (x::xs) = expr x :: args xs

expr (MkVect fc _ xs)
  = vect (args xs)
  where args : Vect.Quantifiers.All.All Exprs.Expr as -> List (Doc ())
        args [] = []
        args (x::xs) = expr x :: args xs

expr (GetV fc idx tm)
  = duo "get" (pretty idx) (expr tm)

expr (SetV fc idx tm v)
  = tri "set" (pretty idx) (expr tm) (expr v)

expr (Slice fc st ed tm)
  = tri "slice" (expr st) (expr ed) (expr tm)

expr (GetL fc idx tm)
  = duo "get" (expr idx) (expr tm)

expr (SetL fc idx tm v)
  = tri "set" (expr idx) (expr tm) (expr v)

expr (MkTuple fc prf ars)
  = group
  $ hcat
  [ tupled (args ars)
  ]
  where args : Vect.Quantifiers.All.All Exprs.Expr as -> List (Doc ())
        args [] = []
        args (x::xs) = expr x :: args xs

expr (GetT fc loc tup)
  = group
  $ hcat
  [ pretty "project"
  , brackets (pretty loc)
  , parens (expr tup)
  ]

expr (SetT fc loc tup v)
  = group
  $ hcat
  [ pretty "replace"
  , brackets (pretty loc)
  , tupled [expr tup, expr v]
  ]

expr (Record fc prf fs)
  = group
  $ hcat
    [ brackets
      $ hsep (fields fs)
    ]
  where fields : Vect.Quantifiers.All.All Field fss -> List (Doc ())
        fields []
          = Nil
        fields ((F x s e) :: y)
          = (group
          $ hsep [ binderValue s, equals, expr e])
          :: fields y


expr (GetR fc loc tup)
  = group
  $ hcat
  [ (expr tup)
  , dot
  , brackets (pretty loc)
  ]

expr (SetR fc loc tup v)
  = group
  $ hcat
  [ pretty "replace"
  , brackets (pretty loc)
  , tupled [expr tup, expr v]
  ]

expr (Match fc cond prf cs)
  = vcat
  $
  [ hsep [ pretty "match"
         , expr cond
         ]
  , lbrace
  ]
  ++
  map (indent 2) (cases cs)
  ++
  [ rbrace
  ]

  where cases : Vect.Quantifiers.All.All Case fss -> List (Doc ())
        cases []
          = Nil
        cases ((C x t s c)::xs)
          = (vcat
          [ group
            $ hsep
              [ hcat [ binderValue t
                     , parens
                       $ binderValue s
                      ]
              , pretty "=>"
              ]
          , indent 2 (expr c)
          ])
          :: cases xs

expr (Tag fc s tm)
  = group
  $ hcat
  [ pretty s
  , parens (expr tm)
  ]

expr (The fc ty tm)
  = hsep
    [ expr tm
    , colon
    , type ty
    ]

expr (Cond fc c t f)
  = cond (expr c) (expr t) (expr f)

expr (Seq fc this that)
  = vcat [ hcat [expr this, semi], expr that]

expr (ForEach fc (MkRef fc s) R cond scope)
  = vcat
  [ hsep
    [ pretty "for"
    , binderValue s
    , pretty "in"
    , hcat
      [expr cond
      , dot
      , pretty "iter()"
      ]
    ]
  , lbrace
  , indent 2 (expr scope)
  , rbrace
  ]

expr (Loop fc scope c)
  = vcat
  [ pretty "loop"
  , lbrace
  , indent 2 (expr scope)
  , indent 2
    $ cond (expr c) (pretty "break;") (pretty "continue;")
  , rbrace
  ]

expr (Call fc fun prf x argz)
  = group
  $ hcat
  [ refValue fun
  , tupled (args argz)
  ]
  where args : Vect.Quantifiers.All.All Exprs.Expr as -> List (Doc ())
        args [] = []
        args (x::xs) = expr x :: args xs

expr (Run fc fun prfR prfA argz prfV valz)
  = group
  $ hsep
  [ keyword "run"
  , hcat [ref fun, tupled $ args argz]
  , keyword "with"
  , list (vals valz)]
  where args : Vect.Quantifiers.All.All Exprs.Expr as -> List (Doc ())
        args [] = []
        args (x::xs) = expr x :: args xs

        vals : Vect.Quantifiers.All.All Val as -> List (Doc ())
        vals [] = []
        vals ((V x r str)::xs)
          = (group
          $ hsep [role r, keyword "as", expr str]
          ) :: vals xs

-}


function : Fun f -> Doc ()
function (Func fc prf as ret scope)
  = vcat
    [ hsep
      [ tupled
        $ fargs as
      , pretty "->"
      , type ret]
    , lbrace
    , align $ indent 2 (expr scope)
    , rbrace
    ]



role : Role r -> Doc ()
role (R s) = pretty s

protocol : Protocol p -> Doc ()

protocol (End fc)
  = pretty "end"

protocol (Call fc r prf)
  = uno "call" (refValue r)

protocol (Rec fc r prf scope)
  = vsep
    [ hcat
      [ pretty "rec"
      , parens (refValue r)
      ]
    , hsep
      [ dot
      , protocol scope
      ]
    ]

protocol (Choice fc s r t prf (B1 (x::xs)))
  = vsep
  $ [ hsep
      [ role s
      , pretty "==>"
      , role r
      , brackets (type t)
      , lbrace
      , branch x
      ]
    ]
  ++ branches xs
  ++ [ rbrace ]
  where branch : forall b . Branch b -> Doc ()
        branch (B y label ty cont)
          = vcat
            [ group
              $ hcat
                [ binderValue label
                , parens
                  $ type ty
                ]
            , hsep
              [ dot
              , protocol cont
              ]
            ]

        branches : Vect.Quantifiers.All.All Branch bs -> List (Doc ())
        branches []
          = []
        branches (x :: y)
          = hsep
          [ pipe
          , branch x]
          ::
          branches y


sexpr : Sessions.Expr b -> Doc ()
sexpr _ = pretty "// TODO"
{-
sexpr (Seq fc x y)
  = vcat
  [ hcat [expr x, semi]
  , sexpr y]

sexpr (Hole ref prf)
  = hole ref

sexpr (LetTy fc s st ty val scope)
  = vsep
  [ group
    $ hsep
      [ keyword (stored st)
      , binder s
      , colon
      , type ty
      , equals
      , expr val
      , semi
      ]
  , sexpr scope
  ]

sexpr (Let fc s st val scope)
  = vsep
  [ group
    $ hsep
      [ keyword (stored st)
      , binder s
      , equals
      , expr val
      , semi
      ]
  , sexpr scope
  ]

sexpr (LetRec fc s scope)
  = vsep
  [ hcat [ keyword "loop"
         , parens (binder s)
         ]
  , lbrace
  , indent 2 (sexpr scope)
  , rbrace
  ]

sexpr (Call fc s)
  = uno "call" (binder s)

sexpr (Split fc ss val scope)
  = vsep
  [ group
    $ hsep
      [ keyword "local"
      , hcat
        [ keyword "tuple"
        , tupled $ map pretty ss
        ]
      , equals
      , expr val
      , semi
      ]
  , sexpr scope
  ]

sexpr (Crash fc e)
  = uno "crash" (expr e)

sexpr (End fc e)
  = uno "end" (expr e)

sexpr (Cond fc cond tt ff)
  = vsep
  [ hsep [ keyword "if"
         , expr cond
         ]
  , lbrace
  , indent 2 (sexpr tt)
  , hsep [ rbrace
         , keyword "else"
         ]
  , lbrace
  , indent 2 (sexpr ff)
  , rbrace
  ]

sexpr (Match fc cond prf offs)
  = vcat
  $
  [ hsep [ keyword "match"
         , expr cond
         ]
  , lbrace
  ]
  ++
  map (indent 2) (cases offs)
  ++
  [ rbrace
  ]

  where cases : Vect.Quantifiers.All.All Offer fss -> List (Doc ())
        cases []
          = Nil
        cases ((O x t s c)::xs)
          = (vcat
          [ group
            $ hsep
              [ keyword "when"
              , hcat
                [ pretty t
                , parens
                  $ pretty s
                ]
              ]
          , lbrace
          , indent 2 (sexpr c)
          , rbrace
          ])
          :: cases xs

sexpr (Read fc r ty prf offs onEr)
  = vcat
  $
  [ hsep [ keyword "recv"
         , brackets (type ty)
         , role r
         ]
  , lbrace
  ]
  ++
  map (indent 2) (cases offs)
  ++
  [ hsep [ rbrace
         , keyword "catch"]
  , lbrace
  , indent 2 (sexpr onEr)
  , rbrace
  ]

  where cases : Vect.Quantifiers.All.All Offer fss -> List (Doc ())
        cases []
          = Nil
        cases ((O x t s c)::xs)
          = (vcat
          [ group
            $ hsep
              [ keyword "when"
              , hsep [ pretty t
                     , parens
                       $ pretty s
                     ]
              ]
          , lbrace
          , indent 2 (sexpr c)
          , rbrace
          ])
          :: cases xs

sexpr (Send fc r ty s msg body exc)
  = align
  $ vcat
  $
  [ hsep [ keyword "send"
         , brackets (type ty)
         , role r
         , group (hcat [binder s, parens (expr msg)])
         ]
  , align
    $ indent 2
    $ vsep
      [ (keyword "catch")
      , lbrace
      , indent 2 (sexpr exc)
      , rbrace
      ]
  , sexpr body
  ]
-}


session : String -> Session p -> Doc ()
session n (Sesh fc prin r x prf args ret scope)
  = vcat
  [ hsep [ pretty "//"
         , refType r
         , pretty "as"
         , role prin
         ]
  , hsep [ pretty "fn"
         , pretty n
         , tupled
           $ fargs args
         , pretty "->"
         , type ret
         ]
  , lbrace
  , indent 2 (sexpr scope)
  , rbrace
  ]




program : Prog p -> List (Doc ())
program (Main fc m)
  = [ hsep
      [ binderValue "capableMain"
      , function m
      ]
    ]

program (Def fc DTYPE s val scope)
  = (::) (datatype s val)
         (program scope)

program (Def fc TYPE s val scope)
  = (::) (hsep
          [ pretty "type"
          , binderType s
          , equals
          , type val
          ]
         )
         (program scope)

program (Def fc FUNC s val scope)
  = (::) (hsep
          [ pretty "fn"
          , binderValue s
          , function val
          ]
          )
          (program scope)

program (Def fc ROLE s val scope)
  = (::) (hsep
          [ pretty "//"
          , pretty "role"
          , pretty s
          ]
         )
         (program scope)

program (Def fc PROT s val scope)
  = (::) (vsep
          [ pretty "/*"
          , hsep
            [ pretty "protocol"
            , binderType s
            ]
          , indent 2
            $ hsep
              [ equals
              , protocol val
              ]
          , pretty "*/"
          ]
        )
        (program scope)

program (Def fc SESH s val scope)
  = (::) (session s val)
         (program scope)

ourMain : Doc ()
ourMain
  = pretty """
           fn main ()
           {
             let args : Vec<String> = env::args().collect();
             capableMain(args)
           }
           """

ourHeader : Doc ()
ourHeader
  = pretty """
           use std::env;
           """

everything : Prog p -> Doc ()
everything p
  = vsep
  $ punctuate hardline
              (ourHeader
               :: (program p)
               ++ [ ourMain ]
              )




export
codegen : (ast : Prog p) -> String
codegen
  = (show . everything)


-- [ EOF ]
