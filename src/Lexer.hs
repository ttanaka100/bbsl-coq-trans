module Lexer where

import qualified Data.Text             as T
import           Text.Parsec
import qualified Text.Parsec.Expr      as Ex
import           Text.Parsec.String
import qualified Text.Parsec.Token     as Tok

import           Data.Functor.Identity

type Op a = Ex.Operator String () Identity a
type Operators a = Ex.OperatorTable String () Identity a

reservedNames :: [String]
reservedNames = [
    "exfunction",
    "endexfunction",
    "condition",
    "endcondition",
    "none",
    "forall",
    "exists",
    "∈",
    "PROJx",
    "PROJy",
    "PROJxu",
    "PROJyu",
    "PROJxl",
    "PROJyl",
    "RAT",
    "w",
    "case",
    "endcase",
    "let",
    "in",
    "setBB",
    "bb",
    "interval",
    "real",
    "bool"
  ]

reservedOps :: [String]
reservedOps = [
    "=",
    "<",
    ">",
    "\8776",
    "⊂",
    "⊃",
    "⊆",
    "⊇",
    "∪",
    "∩",
    "not",
    "and",
    "or"
  ]

lexer :: Tok.GenTokenParser String () Identity
lexer = Tok.makeTokenParser $ Tok.LanguageDef
  { Tok.commentStart    = "(*"
  , Tok.commentEnd      = "*)"
  , Tok.commentLine     = "//"
  , Tok.nestedComments  = True
  , Tok.identStart      = letter
  , Tok.identLetter     = alphaNum <|> oneOf "_'"
  , Tok.opStart         = oneOf "≈:!#$%&*+./<=>?@\\^|-~"
  , Tok.opLetter        = oneOf "≈:!#$%&*+./<=>?@\\^|-~"
  , Tok.reservedNames   = reservedNames
  , Tok.reservedOpNames = reservedOps
  , Tok.caseSensitive   = True
  }

reserved :: String -> Parser ()
reserved = Tok.reserved lexer

reservedOp :: String -> Parser ()
reservedOp = Tok.reservedOp lexer

identifier :: Parser String
identifier = Tok.identifier lexer

parens :: Parser a -> Parser a
parens = Tok.parens lexer

commaSep :: Parser a -> Parser [a]
commaSep = Tok.commaSep lexer

brackets :: Parser a -> Parser a
brackets = Tok.brackets lexer

comma :: Parser String
comma = Tok.comma lexer

colon :: Parser String
colon = Tok.colon lexer

dot :: Parser String
dot = Tok.dot lexer

contents :: Parser a -> Parser a
contents p = do
  Tok.whiteSpace lexer
  r <- p
  eof
  return r
