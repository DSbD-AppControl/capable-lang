||| Pretty Print Capable Programs.
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Capable.Pretty

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
import Capable.Raw.Exprs
import Capable.Raw.Funcs
import Capable.Raw.Sessions
import Capable.Raw.Progs

%default total


data KIND = KEYWORD
          | BOUND
          | VALUE
          | TYPE
          | ROLE
          | HOLE
          | TODO
          | ESCAPE

command : String -> Doc ann -> Doc ann
command k v
  = group
  $ hcat
  [ backslash
  , pretty k
  , braces v]

escape : Doc KIND -> Doc KIND
escape
  = id

lbrace' : Doc KIND
lbrace' = escape lbrace

rbrace' : Doc KIND
rbrace' = escape rbrace

keyword : String -> Doc KIND
keyword
  = (annotate KEYWORD . pretty)

binder : String -> Doc KIND
binder
  = (annotate BOUND . pretty)

value : Doc KIND -> Doc KIND
value
  = annotate VALUE

typeStr : String -> Doc KIND
typeStr
  = (annotate TYPE . pretty)

typeDoc : Doc KIND -> Doc KIND
typeDoc
  = annotate TYPE

ref : Ref -> Doc KIND
ref = binder . get

role : Role r -> Doc KIND
role (R s) = annotate ROLE (pretty s)

hole : Ref -> Doc KIND
hole r
  = annotate Pretty.HOLE
  $ pretty "?" <+> ref r

kvs : (forall t . Ty t -> Doc KIND) -> Named.Args fs -> List (Doc KIND)
kvs _ []
  = []

kvs ann (Add fc s ty rest)
  = (group $ hsep [binder s, typeDoc colon, ann ty])  :: kvs ann rest


tuple : (forall t . Ty t -> Doc KIND)
     -> Types.Args fs'
     -> List (Doc KIND)
tuple f []
  = []

tuple f (ty :: rest)
  = f ty :: tuple f rest

typeFields : List (Doc KIND) -> Doc KIND
typeFields
  = group . encloseSep (flatAlt (typeStr "{ ") (typeStr "{"))
                       (flatAlt (typeStr " }") (typeStr "}"))
                       (typeStr "; ")

type : Ty t -> Doc KIND
type (TyVar r prf)
  = typeDoc $ ref r

type (TyChar fc)
  = typeStr  "Char"

type (TyStr fc)
  = typeStr "String"

type (TyInt fc)
  = typeStr "Int"

type (TyBool fc)
  = typeStr "Bool"

type (TyUnit fc)
  = typeStr "Unit"

type (TyArray fc n ty)
  = group
  $ brackets {ldelim=typeDoc lbracket} {rdelim=typeDoc rbracket}
  $ hcat
  [ pretty n
  , typeDoc semi
  , type ty
  ]

type (TyTuple fc prf fs)
  = tupled (assert_total $ tuple type fs)

  where tupled : List (Doc KIND) -> Doc KIND
        tupled = group . encloseSep (flatAlt (typeStr "( ") (typeStr "("))
                                    (flatAlt (typeStr " )") (typeStr ")"))
                                    (typeStr ", ")

type (TyData fc STRUCT prf fs)
  = group
  $ hsep
  [ typeStr "struct"
  , typeFields $ assert_total $ kvs type fs]

type (TyData fc UNION prf fs)
  = group
  $ hsep
  [ typeStr "union"
  , typeFields $ assert_total $ kvs type fs]

type (TyRef fc ty)
  = group
  $ hcat
  [ pretty "&"
  , type ty
  ]

type (TyHandle fc FILE)
  = pretty "FILE"
type (TyHandle fc PROCESS)
  = pretty "PROC"

farg : Arg a -> Doc KIND
farg (A fc n ty)
  = hsep
  [ binder n
  , assert_total $ type ty
  ]


fargs : Vect.Quantifiers.All.All Arg az -> List (Doc KIND)
fargs []
  = Nil

fargs (x :: y)
  = farg x :: fargs y

uno : String
   -> Doc KIND
   -> Doc KIND
uno f a
  = group
  $ hcat
  [ keyword f
  , parens a
  ]

duo : String
   -> Doc KIND
   -> Doc KIND
   -> Doc KIND
duo f a b
  = group
  $ hcat
  [ keyword f
  , tupled [a,b]
  ]

tri : String
   -> Doc KIND
   -> Doc KIND
   -> Doc KIND
   -> Doc KIND
tri f a b c
  = group
  $ hcat
  [ keyword f
  , tupled [a, b, c]
  ]

stored : Stored -> String
stored HEAP  = "val"
stored STACK = "local"

prettyMode : Mode -> Doc KIND
prettyMode Read              = "r"
prettyMode WriteTruncate     = "w"
prettyMode Append            = "a"
prettyMode ReadWrite         = "r+"
prettyMode ReadWriteTruncate = "w+"
prettyMode ReadAppend        = "a+"

handlekind : HandleKind -> Doc KIND
handlekind FILE = keyword "fopen"
handlekind PROCESS = keyword "popen"

structs : List (Doc KIND) -> Doc KIND
structs
  = group . encloseSep (flatAlt (typeStr "{ ") (typeStr "{"))
                       (flatAlt (typeStr " }") (typeStr "}"))
                       (typeStr ", ")

expr : Raw.Exprs.Expr b -> Doc KIND
expr (Hole ref prf)
  = hole ref

expr (Var r prf)
  = ref r

expr (LetTy fc s st ty val scope)
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
  , expr scope
  ]
expr (Let fc s st val scope)
  = vsep
  [ group
    $ hsep
      [ keyword (stored st)
      , binder s
      , equals
      , expr val
      , semi
      ]
  , expr scope
  ]

expr (Split fc ss val scope)
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
  , expr scope
  ]

expr (Const fc UNIT v) = value (pretty "unit")
expr (Const fc CHAR v) = value (squotes $ v' v)
  where v' : Char -> Doc KIND
        v' c = if isNL c then pretty "\\n" else pretty c

expr (Const fc STR v) = value (dquotes $ pretty v)
expr (Const fc INT v) = value (pretty v)
expr (Const fc BOOL v) = value (pretty v)

expr (OpBin fc WRITE l r)   = duo "write" (expr l) (expr r)
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
expr (OpUn fc FETCH o)      = uno "!" (expr o)
expr (OpUn fc READ o)       = uno "read" (expr o)
expr (OpUn fc CLOSE o)      = uno "close" (expr o)
expr (OpUn fc NOT o)        = uno "not" (expr o)
expr (OpUn fc SIZE o)       = uno "size" (expr o)
expr (OpUn fc ORD o)        = uno "ord" (expr o)
expr (OpUn fc CHR o)        = uno "chr" (expr o)
expr (OpUn fc STRO o)       = uno "string" (expr o)
expr (OpUn fc TOSTR o)      = uno "toString" (expr o)
expr (OpUn fc (OPEN x y) o)
  = group
  $ (handlekind x <+> tupled [prettyMode y, expr o])

-- @TODO
expr (ArrayEmpty fc) = lbrace'
expr (ArrayCons fc head tail)
  = annotate TODO (expr head <+> comma <+> expr tail)

expr (Index fc idx tm)
  = duo "index" (expr idx) (expr tm)

expr (Slice fc st ed tm)
  = tri "slice" (expr st) (expr ed) (expr tm)

expr (MkTuple fc prf ars)
  = group
  $ hcat
  [ keyword "tuple"
  , tupled (args ars)
  ]
  where args : Vect.Quantifiers.All.All Exprs.Expr as -> List (Doc KIND)
        args [] = []
        args (x::xs) = expr x :: args xs

expr (Get fc loc tup)
  = group
  $ hcat
  [ keyword "get"
  , brackets (pretty loc)
  , parens (expr tup)
  ]

expr (Set fc loc tup v)
  = group
  $ hcat
  [ keyword "set"
  , brackets (pretty loc)
  , tupled [expr tup, expr v]
  ]

expr (Record fc prf fs)
  = group
  $ hcat
  [ keyword "struct"
  , brackets (annotate TODO (pretty "ADD TYPES"))
  , structs (fields fs)
  ]
  where fields : Vect.Quantifiers.All.All Field fss -> List (Doc KIND)
        fields []
          = Nil
        fields ((F x s e) :: y)
          = (group
          $ hsep [ binder s, equals, expr e])
          :: fields y


expr (GetR fc loc tup)
  = group
  $ hcat
  [ keyword "get"
  , brackets (pretty loc)
  , parens (expr tup)
  ]

expr (SetR fc loc tup v)
  = group
  $ hcat
  [ keyword "set"
  , brackets (pretty loc)
  , tupled [expr tup, expr v]
  ]

expr (Match fc cond prf cs)
  = vcat
  $
  [ hsep [ keyword "match"
         , expr cond
         ]
  , lbrace'
  ]
  ++
  map (indent 2) (cases cs)
  ++
  [ rbrace'
  ]

  where cases : Vect.Quantifiers.All.All Case fss -> List (Doc KIND)
        cases []
          = Nil
        cases ((C x t s c)::xs)
          = (vcat
          [ group
            $ hsep
              [ keyword "when"
              , hcat [ pretty t
                     , parens
                       $ pretty s
                      ]
              ]
          , lbrace'
          , indent 2 (expr c)
          , rbrace'
          ])
          :: cases xs

expr (Tag fc s tm)
  = group
  $ hcat
  [ keyword "tag"
  , brackets (pretty s)
  , parens (expr tm)
  ]

expr (The fc ty tm)
  = duo "the" (type ty) (expr tm)

expr (Cond fc c t f)
  = vsep
  [ hsep [ keyword "if", expr c]
  , lbrace'
  , indent 2 (expr t)
  , hsep [ rbrace' , keyword "else" ]
  , lbrace'
  , indent 2 (expr f)
  , rbrace'
  ]

expr (Seq fc this that)
  = vcat [ hcat [expr this, semi], expr that]

expr (Loop fc scope cond)
  = vcat
  [ keyword "loop"
  , lbrace'
  , indent 2 (expr scope)
  , hcat [ rbrace', keyword "until", expr cond]
  ]

expr (Call fc fun prf x argz)
  = group
  $ hcat
  [ ref fun
  , tupled (args argz)
  ]
  where args : Vect.Quantifiers.All.All Exprs.Expr as -> List (Doc KIND)
        args [] = []
        args (x::xs) = expr x :: args xs

expr (Run fc fun prfR prfA argz prfV valz)
  = group
  $ hsep
  [ keyword "run"
  , hcat [ref fun, tupled $ args argz]
  , keyword "with"
  , list (vals valz)]
  where args : Vect.Quantifiers.All.All Exprs.Expr as -> List (Doc KIND)
        args [] = []
        args (x::xs) = expr x :: args xs

        vals : Vect.Quantifiers.All.All Val as -> List (Doc KIND)
        vals [] = []
        vals ((V x r str)::xs)
          = (group
          $ hsep [role r, keyword "as", expr str]
          ) :: vals xs

function : Fun f -> Doc KIND
function (Func fc prf as ret scope)
  = vcat
  [ hsep [tupled $ fargs as, pretty "->", type ret]
  , lbrace'
  , align $ indent 2 (expr scope)
  , rbrace'
  ]

protocol : Protocol p -> Doc KIND
protocol (End fc)
  = keyword "end"

protocol (Call fc r prf)
  = uno "call" (ref r)

protocol (Rec fc r prf scope)
  = vsep
  [ hcat [ keyword "rec"
         , parens (ref r)
         ]
  , hsep [ dot
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
      , lbrace'
      , branch x
      ]
    ]
  ++ branches xs
  ++ [ rbrace' ]
  where branch : forall b . Branch b -> Doc KIND
        branch (B y label ty cont)
          = vcat
          [ group
            $ hcat
              [ binder label
              , parens
                $ type ty
              ]
          , hsep [ dot
                 , protocol cont
                 ]
          ]

        branches : Vect.Quantifiers.All.All Branch bs -> List (Doc KIND)
        branches []
          = []
        branches (x :: y)
          = hsep
          [ pipe
          , branch x]
          ::
          branches y


sexpr : Sessions.Expr b -> Doc KIND
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
  , lbrace'
  , indent 2 (sexpr scope)
  , rbrace'
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
  , lbrace'
  , indent 2 (sexpr tt)
  , hsep [ rbrace'
         , keyword "else"
         ]
  , lbrace'
  , indent 2 (sexpr ff)
  , rbrace'
  ]

sexpr (Match fc cond prf offs)
  = vcat
  $
  [ hsep [ keyword "match"
         , expr cond
         ]
  , lbrace'
  ]
  ++
  map (indent 2) (cases offs)
  ++
  [ rbrace'
  ]

  where cases : Vect.Quantifiers.All.All Offer fss -> List (Doc KIND)
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
          , lbrace'
          , indent 2 (sexpr c)
          , rbrace'
          ])
          :: cases xs

sexpr (Read fc r ty prf offs onEr)
  = vcat
  $
  [ hsep [ keyword "recv"
         , brackets (type ty)
         , role r
         ]
  , lbrace'
  ]
  ++
  map (indent 2) (cases offs)
  ++
  [ hsep [ rbrace'
         , keyword "catch"]
  , lbrace'
  , indent 2 (sexpr onEr)
  , rbrace'
  ]

  where cases : Vect.Quantifiers.All.All Offer fss -> List (Doc KIND)
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
          , lbrace'
          , indent 2 (sexpr c)
          , rbrace'
          ])
          :: cases xs

sexpr (Send fc r ty s msg body exc)
  = vcat
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
      , lbrace'
      , indent 2 (sexpr exc)
      , rbrace'
      ]
  ]

session : Session p -> Doc KIND
session (Sesh fc prin r x prf args ret scope)
  = vcat
  [ hsep [ group $ angles (hsep [ref r, keyword "as", role prin])
         , tupled $ fargs args, pretty "->", type ret]
  , lbrace'
  , indent 2 (sexpr scope)
  , rbrace'
  ]

prog : Prog p -> Doc KIND
prog (Main fc m)
  = hsep
  [ binder "main"
  , function m
  ]

prog (Def fc TYPE s val scope)
  = vsep
  [ hsep [ keyword "type"
         , binder s
         , equals
         , type val]
  , prog scope]

prog (Def fc FUNC s val scope)
  = vsep
  [ hsep [keyword "func", binder s, function val]
  , prog scope]

prog (Def fc ROLE s val scope)
  = vsep
  [ hsep [ keyword "role"
         , annotate ROLE $ pretty s
         ]
  , prog scope
  ]

prog (Def fc PROT s val scope)
  = vsep
  [ hsep
    [ keyword "protocol"
    , binder s
    ]
  , indent 2
    $ hsep
      [ equals
      , protocol val
      ]
  , prog scope
  ]

prog (Def fc SESH s val scope)
  = vsep
  [ hsep [ keyword "session"
         , binder s
         , session val
         ]
  , prog scope
  ]



program : (p : PROG) -> Doc KIND
program p = prog (toProg p)

export
toString : (p : PROG) -> String
toString
  = (show . reAnnotate (const ()) . program)


renderAs : (Char -> String)
        -> (ann -> String)
        -> String
        -> SimpleDocStream ann
        -> String

renderAs e f g SEmpty
  = neutral

renderAs e f g (SChar c rest)
  = (e c) <+> renderAs e f g rest

renderAs e f g (SText l t rest)
  = purge t <+> renderAs e f g rest

  where purge : String -> String
        purge = (foldr (<+>) "" . map e . unpack)

renderAs e f g (SLine l rest)
  =   singleton '\n'
  <+> textSpaces l
  <+> renderAs e f g rest

renderAs e f g (SAnnPush ann rest)
  = f ann <+> renderAs e f g rest

renderAs e f g (SAnnPop rest)
  = g <+> renderAs e f g rest

export
toLaTeX : (p : PROG) -> String
toLaTeX
  = (env . renderAs e foo "}" . layoutPretty defaultLayoutOptions . program)

  where cmd : String -> String
        cmd s = "\\Capable\{s}{"

        e : Char -> String
        e '_' =  "\\_"
        e '{' = "\\{"
        e '}' = "\\}"
        e c
          = if isNL c
            then "\\newline"
            else cast c

        foo : KIND -> String
        foo KEYWORD
          = cmd "Keyword"
        foo BOUND
          = cmd "Bound"
        foo VALUE
          = cmd "Value"
        foo TYPE
          = cmd "Type"
        foo ROLE
          = cmd "Role"
        foo HOLE
          = cmd "Hole"
        foo TODO
          = cmd "TODO"
        foo ESCAPE
          = ""

        env : String -> String
        env d
          = unlines
          [ "\\begin{VerbatimInline}"
          , d
          , "\\end{VerbatimInline}"
          ]

-- [ EOF ]
