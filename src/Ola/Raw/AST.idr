|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Ola.Raw.AST

import System.File.Mode

import public Toolkit.Data.Location
import public Toolkit.AST

import Ola.Types

%default total

namespace Kind
  public export
  data Kind = ROLE
            | PROT
            | BRANCH
            | TYPE
            | EXPR
            | FUNC
            | ARG
            | ARGS
            | PROG


namespace Expr
  public export
  data PrimVal = UNIT | CHAR | STR | INT | BOOL

  export
  Show PrimVal where
    show UNIT = "UNIT"
    show CHAR = "CHAR"
    show STR  = "STR"
    show INT  = "INT"
    show BOOL = "BOOL"

  public export
  InterpPVal : PrimVal -> Type
  InterpPVal UNIT = ()
  InterpPVal CHAR = Char
  InterpPVal STR = String
  InterpPVal INT = Int
  InterpPVal BOOL = Bool

  public export
  data BuiltinUnOps = PRINT
                    | FETCH
                    | READ
                    | CLOSE
                    | NOT
                    | SIZE
                    | ORD
                    | CHR
                    | STRO
                    | TOSTR
                    | OPEN HandleKind Mode

  export
  Show BuiltinUnOps where
    show FETCH = "FETCH"
    show READ  = "READ"
    show CLOSE = "CLOSE"
    show PRINT = "PRINT"
    show NOT   = "NOT"
    show SIZE  = "SIZE"
    show ORD   = "ORD"
    show CHR   = "CHR"
    show STRO  = "STR"
    show TOSTR = "TOSTR"
    show (OPEN k m) = "(OPEN \{show k} MODE...)"

  public export
  data BuiltinBinOps = WRITE
                     | AND
                     | OR
                     | LT
                     | LTE
                     | EQ
                     | GT
                     | GTE
                     | ADD
                     | SUB
                     | MUL
                     | DIV
                     | STRCONS
                     | MUT
  export
  Show BuiltinBinOps where
    show WRITE = "WRITE"
    show STRCONS = "STRCONS"
    show AND = "AND"
    show OR  = "OR"
    show LT  = "LT"
    show LTE = "LTE"
    show EQ  = "EQ"
    show GT  = "GT"
    show GTE = "GTE"
    show ADD = "ADD"
    show SUB = "SUB"
    show MUL = "MUL"
    show DIV = "DIV"
    show MUT = "MUT"

  public export
  data Stored = HEAP | STACK

  export
  Show Stored where
    show HEAP = "HEAP"
    show STACK = "STACK"

  public export
  data DefKind : Kind.Kind -> Type where
    TYPE : DefKind TYPE
    FUNC : DefKind FUNC
    ROLE : DefKind ROLE
    PROT : DefKind PROT

  export
  Show (DefKind k) where
    show TYPE = "TYPE"
    show FUNC = "FUNC"
    show ROLE = "ROLE"
    show PROT = "PROT"

namespace Shape
  public export
  data Shape : SHAPE Kind.Kind where
    -- ## Roles
    ROLE : String -> NULL Shape ROLE

    -- ## Protocols
    STOP : NULL Shape PROT
    CALLP : String -> NULL Shape PROT
    RECP  : String -> UN Shape PROT PROT
    BRANCHP : String -> BIN Shape BRANCH TYPE PROT
    CHOICE : Shape PROT (S (S (S n))) (ROLE::ROLE::replicate (S n) BRANCH)

    -- ## Types
    CHAR, STR, INT, BOOL, UNIT : NULL Shape TYPE

    HANDLE : HandleKind -> NULL Shape TYPE
    VARTY  : String -> NULL Shape TYPE
    REF    : UN Shape TYPE TYPE
    ARRAY  : Int -> UN Shape TYPE TYPE

    PROD,UNION : BIN Shape TYPE TYPE TYPE

    ARROW : Shape TYPE (S n) (replicate (S n) TYPE)

    -- ## Expressions

    -- ### Bindings
    VAR : String -> NULL Shape EXPR
    LETTY : Stored -> String -> TRI Shape EXPR TYPE EXPR EXPR
    LET   : Stored -> String -> BIN Shape EXPR      EXPR EXPR

    -- ### Builtins...

    CONST : (p : PrimVal)
         -> (v : InterpPVal p)
              -> NULL Shape EXPR

    BBIN : (k : BuiltinBinOps)
             -> BIN Shape EXPR EXPR EXPR

    BUN : (k : BuiltinUnOps)
            -> UN Shape EXPR EXPR

    -- ### Data
    -- #### Arrays
    NIL   : NULL Shape EXPR
    CONS  : BIN Shape EXPR EXPR EXPR
    IDX   : BIN Shape EXPR EXPR EXPR
    SLICE : TRI Shape EXPR EXPR EXPR EXPR

    -- #### Products
    PAIR : BIN Shape EXPR EXPR EXPR
    SPLIT : String -> String -> BIN Shape EXPR EXPR EXPR

    -- #### Unions
    LEFT  : UN Shape EXPR EXPR
    RIGHT : UN Shape EXPR EXPR
    MATCH : String -> String -> TRI Shape EXPR EXPR EXPR EXPR

    -- ### Ascriptions
    THE : BIN Shape EXPR TYPE EXPR

    -- ### Control Flow
    COND : TRI Shape EXPR EXPR EXPR EXPR
    SEQ  : BIN Shape EXPR EXPR EXPR
    LOOP : BIN Shape EXPR EXPR EXPR

    -- ### Application
    CALL : Shape EXPR (S n) (EXPR::replicate n EXPR)

    -- ## Functions
    ARG : String -> UN Shape ARG TYPE
    ARGS : Shape ARGS n (replicate n ARG)
    FUN : TRI Shape FUNC ARGS TYPE EXPR

    -- ## Programs

    MAIN : UN Shape PROG FUNC
    DEF : String -> DefKind k -> BIN Shape PROG k PROG

namespace FileContext
  public export
  AST : Kind.Kind -> Type
  AST k = AST Shape k FileContext

  namespace Raw
    namespace AST

      public export
      BRANCH : Type
      BRANCH = AST BRANCH

      public export
      PROT : Type
      PROT = AST PROT

      public export
      ROLE : Type
      ROLE = AST ROLE

      public export
      TYPE : Type
      TYPE = AST TYPE

      public export
      EXPR : Type
      EXPR = AST EXPR

      public export
      ARG : Type
      ARG = AST ARG

      public export
      ARGS : Type
      ARGS = AST ARGS

      public export
      FUNC : Type
      FUNC = AST FUNC

      public export
      PROG : Type
      PROG = AST PROG

export
setSource : String -> AST a -> AST a
setSource str
  = map (setSource str)

export
getFC : AST a -> FileContext
getFC = getAnnotation

namespace Utils
  export
  roleToRef : AST ROLE -> Ref
  roleToRef (Branch (ROLE str) annot nodes)
    = MkRef annot str

  public export
  data AsVect : (this : DVect Kind.Kind
                              (\k => AST s k a)
                              n
                              (replicate n type))

             -> (that : Vect n (AST s type a))
                     -> Type
    where
      Empty : AsVect Nil Nil
      Next : AsVect xs ys
          -> AsVect (x::xs) (x::ys)

  export
  asVect : (this : DVect Kind.Kind
                         (\k => AST s k a)
                         n
                         (replicate n type))
        -> DPair (Vect n (AST s type a))
                 (AsVect this)
  asVect [] = ([] ** Empty)
  asVect (ex :: rest) with (asVect rest)
    asVect (ex :: rest) | ((fst ** snd))
      = (ex :: fst ** Next snd)

-- [ EOF ]