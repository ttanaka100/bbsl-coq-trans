module BBSLSyntax where

import           Control.Monad
import           Data.List
import qualified Data.Map      as M

data Type = SBB | BB | I | B | Q deriving (Show,Eq)

data BinOp = Cup | Cap
        | Eq | Gt | Lt | Equiv | Subset | Supset | Subseteq | Supseteq
        | And | Or

instance Show BinOp where
    show Cup      = "∪"
    show Cap      = "∩"
    show Eq       = "="
    show Gt       = ">"
    show Lt       = "<"
    show Equiv    = "\8776"
    show Subset   = "⊂"
    show Supset   = "⊃"
    show Subseteq = "⊆"
    show Supseteq = "⊇"
    show And      = "and"
    show Or       = "or"

data UnOp = Not

instance Show UnOp where
    show Not = "not"

data Res = RAT | W
         | PROJx | PROJy | PROJxu | PROJyu | PROJxl | PROJyl

data Quant = Forall | Exists

data Expr = Var String
          | Val Double
          | BExpr BinOp Expr Expr
          | UExpr UnOp Expr
          | QExpr Quant String Expr Expr
          | Func String [Expr]
          | RFunc Res [Expr]

newtype ExFuncBlock = EFB [ExFunc]
data ExFunc = EF String [Type] Type

newtype SCond = SC Cond
data Cond = None | CND Expr

data Case = Case String CaseDef
type CaseDef = (LetDef, Expr)
newtype LetDef = LD [LetExpr]
data LetExpr = LE String Type Expr

data Spec = Spec ExFuncBlock SCond [Case]

-- show
instance Show Res where
    show RAT    = "RAT"
    show W      = "width"
    show PROJx  = "projx"
    show PROJy  = "projy"
    show PROJxu = "projxu"
    show PROJyu = "projyu"
    show PROJxl = "projxl"
    show PROJyl = "projyl"

instance Show Quant where
    show Forall = "forall"
    show Exists = "exists"

instance Show Expr where
    show (Var x) = x
    show (Val n) = show n
    show (BExpr binop e1 e2) = "(" ++ show e1 ++ ") " ++ show binop ++ " (" ++ show e2 ++ ")"
    show (UExpr unop e) = show unop ++ " (" ++ show e ++ ")"
    show (QExpr q x set body) = show q ++ " " ++ x ++ " ∈ " ++ show set ++ " (" ++ show body ++ ")"
    show (Func f es) = f ++ "(" ++ intercalate "," [show e | e <- es] ++ ")"
    show (RFunc r es) = show r ++ "(" ++ intercalate "," [show e | e <- es] ++ ")"

instance Show SCond where
    show (SC c) = "condition" ++ "\n[" ++ show c ++ "]\n" ++ "endcondition"

instance Show Cond where
    show None    = "none"
    show (CND e) = show e

instance Show Case where
    show (Case label (ld,e)) =
        "case " ++ label ++ "\n" ++ show ld ++ "\n" ++ show e ++ "\n" ++ "endcase"

instance Show LetDef where
    show (LD es) = "let\n" ++ intercalate ",\n" [show e | e <- es] ++ "\n" ++ "in"

instance Show LetExpr where
    show (LE x t e) = x ++ " : " ++ show t ++ " = " ++ show e

instance Show Spec where
    show (Spec ef scond cs) =
        show scond ++ "\n" ++ intercalate "\n" [show c | c <- cs]
