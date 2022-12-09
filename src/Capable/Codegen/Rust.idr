module Capable.Codegen.Rust

import Data.Singleton
import Data.String

import Text.PrettyPrint.Prettyprinter

import Toolkit.Data.DVect

import Capable.Core
import Capable.Check.Common

import Capable.Terms

import Capable.State

%default total
%hide types
%hide type

prettyKV : (Doc ann, Doc ann) -> Doc ann
prettyKV (MkPair k v)
  = group
  $ hsep
    [ k
    , colon
    , v
    ]

prettyFunc : Doc ann
          -> List (Doc ann, Doc ann)
          -> Doc ann
          -> Doc ann
prettyFunc n args body
  = vcat
  [ group
  $ hsep
    [ pretty "fn"
    , n
    , prettyArgs args
    ]
  , braces (hang 2 body)
  ]

  where prettyArgs : List (Doc ann, Doc ann) -> Doc ann
        prettyArgs = (parens . hsep . punctuate comma . map prettyKV)

comment : Doc ann -> Doc ann
comment a = hsep [pretty "//", a]

binder : Doc ann
      -> Doc ann
      -> Maybe (Doc ann)
      -> Doc ann
      -> Doc ann
      -> Doc ann
binder kword name type value scope
  = vcat
    [ hsep [ group
           $ maybe (hsep [kword, name])
                   (\x => kword <++> prettyKV (name,x))
                   (type)
           , equals
           , value]
     , scope
    ]

prettyFin : Fin n -> Doc ann
prettyFin x
  = pretty (cast {to=Nat} x)


mutual

  expr : Expr rs ts g ty -> Doc ann
  expr (Hole str) = ?expr_rhs_0
  expr (Var x) = ?expr_rhs_1
  expr (Let x y rest) = ?expr_rhs_2
  expr (Seq this that)
    = vsep [ expr this <++> semi, expr that]

  expr (Builtin desc args) = ?expr_rhs_4
  expr (Cond cond t f)
    = vsep
      [ group
        $ hsep
          [ pretty "if"
          , expr cond
          ]
      , braces (expr t)
      , pretty "else"
      , braces (expr f)
      ]
  expr ArrayEmpty = ?expr_rhs_6
  expr (ArrayCons x y) = ?expr_rhs_7

  expr (Index idx array)
    = hsep [expr array, expr idx]

  expr (Tuple fields)
    = assert_total
    $ tupled (map (\(a ** tm) => expr tm) $ toList fields)

  expr (Set tuple idx value)
    = comment (pretty "not supported, yet..")
  expr (Get tuple idx)
    = group
      $ hcat
        [ expr tuple
        , dot
        , prettyFin idx
        ]

  expr (Record fields) = ?expr_rhs_12
  expr (SetR re idx value) = ?expr_rhs_13
  expr (GetR rec idx) = ?expr_rhs_14
  expr (Tag s value prf) = ?expr_rhs_15
  expr (Match x cases) = ?expr_rhs_16
  expr (Call x y) = ?expr_rhs_17
  expr (The x y) = ?expr_rhs_18
  expr (Loop body x) = ?expr_rhs_19

  func : Func rs ts g ty -> Doc ann
  func (Fun body)
    = hang 2 (expr body)

  codegen : Env rs ts g
         -> Prog rs ts g ty
         -> Doc ann
  codegen env (DefSesh sesh scope)
    = vcat [ comment (pretty "session types was here")
           , codegen env scope
           ]

  codegen env (DefRole rest) = ?codegen_rhs_1

  codegen env (DefType tyRef rest) = ?codegen_rhs_2

  codegen env (DefFunc sig func rest) = ?codegen_rhs_3

  codegen env (Main x)
    = prettyFunc (pretty "main")
                 Nil
                 (func x)

-- [ EOF ]
