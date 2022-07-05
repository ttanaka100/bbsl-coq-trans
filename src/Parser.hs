module Parser where

import           Text.Parsec
import           Text.Parsec.String

import qualified Text.Parsec.Expr   as Ex
import qualified Text.Parsec.Token  as Tok

import qualified Data.Text          as T

import           BBSLSyntax
import           Lexer

real :: Parser Double
real = Tok.float lexer

variable :: Parser Expr
variable = do
    str <- identifier
    return (Var str)

function :: Parser Expr
function = do
    str <- identifier
    args <- parens (commaSep expr)
    return (Func str args)

resFunc :: String -> Res -> Parser Expr
resFunc str r = do
    reserved str
    args <- parens (commaSep expr)
    return (RFunc r args)

res :: Parser Expr
res = resFunc "RAT" RAT
  <|> resFunc "w" W
  <|> try (resFunc "PROJxu" PROJxu)
  <|> try (resFunc "PROJyu" PROJyu)
  <|> try (resFunc "PROJxl" PROJxl)
  <|> try (resFunc "PROJyl" PROJyl)
  <|> try (resFunc "PROJx" PROJx)
  <|> try (resFunc "PROJy" PROJy)

value :: Parser Expr
value = do
    n <- real
    return (Val n)

forall :: Parser Expr
forall = do
    reserved "forall"
    x <- identifier
    reserved "∈"
    set <- expr
    dot
    body <- parens expr
    return (QExpr Forall x set body)

exists :: Parser Expr
exists = do
    reserved "exists"
    x <- identifier
    reserved "∈"
    set <- expr
    dot
    body <- parens expr
    return (QExpr Exists x set body)

bexpr :: Parser Expr
bexpr = parens expr
    <|> forall
    <|> exists
    <|> value
    <|> try res
    <|> try function
    <|> variable

infixOp :: String -> (a -> a -> a) -> Ex.Assoc -> Op a
infixOp x f = Ex.Infix (reservedOp x >> return f)

prefixOp :: String -> (a -> a) -> Op a
prefixOp x f = Ex.Prefix (reservedOp x >> return f)

table :: Operators Expr
table =
    [
        [
            infixOp "∪" (BExpr Cup) Ex.AssocLeft,
            infixOp "∩" (BExpr Cap) Ex.AssocLeft,
            prefixOp "not" (UExpr Not)
        ],
        [
            infixOp "≈" (BExpr Equiv) Ex.AssocLeft,
            infixOp "=" (BExpr Eq) Ex.AssocLeft,
            infixOp "<" (BExpr Lt) Ex.AssocLeft,
            infixOp ">" (BExpr Gt) Ex.AssocLeft,
            infixOp "⊂" (BExpr Subset) Ex.AssocLeft,
            infixOp "⊃" (BExpr Supset) Ex.AssocLeft,
            infixOp "⊆" (BExpr Subseteq) Ex.AssocLeft,
            infixOp "⊇" (BExpr Supseteq) Ex.AssocLeft
        ],
        [
            infixOp "and" (BExpr And) Ex.AssocLeft,
            infixOp "or" (BExpr Or) Ex.AssocLeft
        ]
    ]

expr :: Parser Expr
expr = Ex.buildExpressionParser table bexpr

-- types
typ :: Parser Type
typ = do {reserved "real"; return Q}
  <|> do {reserved "bool"; return B}
  <|> do {reserved "interval"; return I}
  <|> do {reserved "bb"; return BB}
  <|> do {reserved "setBB"; return SBB}

-- exfunction
exfunc :: Parser ExFunc
exfunc = do
    f <- identifier
    tys <- parens (commaSep typ)
    colon
    t <- typ
    return (EF f tys t)

exfuncBlock :: Parser ExFuncBlock
exfuncBlock = do
    reserved "exfunction"
    fts <- many exfunc
    reserved "endexfunction"
    return (EFB fts)

-- senario-condition
scond :: Parser SCond
scond = do
    reserved "condition"
    c <- brackets cond
    reserved "endcondition"
    return (SC c)

cond :: Parser Cond
cond = do {reserved "none"; return None}
    <|> do {e <- expr; return (CND e)}

cas :: Parser Case
cas = do
    reserved "case"
    cn <- identifier
    cd <- casedef
    reserved "endcase"
    return (Case cn cd)

casedef :: Parser CaseDef
casedef = do
    ld <- letdef
    e <- expr
    return (ld, e)

letdef :: Parser LetDef
letdef = do
    reserved "let"
    ds <- commaSep letexpr
    reserved "in"
    return (LD ds)

letexpr :: Parser LetExpr
letexpr = do
    var <- identifier
    colon
    t <- typ
    reservedOp "="
    e <- expr
    return (LE var t e)

spec :: Parser Spec
spec = do
    ef <- exfuncBlock
    sc <- scond
    cs <- many1 cas
    return (Spec ef sc cs)

parseBBSL :: SourceName -> String -> Either ParseError Spec
parseBBSL file text = parse spec file text
