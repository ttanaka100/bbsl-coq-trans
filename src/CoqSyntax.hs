module CoqSyntax where

import           BBSLSyntax
import           Control.Monad
import           Data.List         (intercalate)
import qualified Data.Map          as M
import           Text.Show.Unicode (ushow)

data FType = FT [Type] Type

data TExpr = TVar String Type
           | TVal Double
           | TBExpr BinOp TExpr TExpr Type
           | TUExpr UnOp TExpr Type
           | TForall String TExpr TExpr
           | TExists String TExpr TExpr
           | TFunc String [TExpr] FType
           | TRFunc Res [TExpr]

data TCond = TNone | TCND TExpr
newtype TSCond = TSC TCond

data TCase = TCase String TCaseDef
type TCaseDef = (TLetDef, TExpr)
newtype TLetDef = TLD [TLetExpr]
data TLetExpr = TLE String Type TExpr

data TSpec = TSpec TSCond [TCase]

type VEnv = M.Map String Type
type FEnv = M.Map String FType
type Env = (VEnv,FEnv)
data Error = VarError String | TypeError Expr | ArgsError String
  deriving Show

typeOfRes :: Res -> Type
typeOfRes PROJx = I
typeOfRes PROJy = I
typeOfRes _     = Q

typeOfTExpr :: TExpr -> Type
typeOfTExpr (TVar _ ty)           = ty
typeOfTExpr (TVal _)              = Q
typeOfTExpr (TBExpr _ _ _ ty)     = ty
typeOfTExpr (TUExpr _ _ ty)       = ty
typeOfTExpr (TForall _ _ _)       = B
typeOfTExpr (TExists _ _ _)       = B
typeOfTExpr (TFunc _ _ (FT _ ty)) = ty
typeOfTExpr (TRFunc r _)          = typeOfRes r



checkUExpr :: Env -> UnOp -> Expr -> [(Type,Type)] -> Either Error TExpr
checkUExpr env op e pts = do
    te <- typeExpr env e
    case lookup (typeOfTExpr te) pts of
        Just t -> Right (TUExpr op te t)
        _      -> Left (TypeError e)

checkBExpr :: Env -> BinOp -> Expr -> Expr -> [((Type,Type),Type)] -> Either Error TExpr
checkBExpr env op e1 e2 pts = do
    te1 <- typeExpr env e1
    te2 <- typeExpr env e2
    let t1 = typeOfTExpr te1
    let t2 = typeOfTExpr te2
    case lookup (t1,t2) pts of
        Just t -> Right (TBExpr op te1 te2 t)
        _      -> Left (TypeError (BExpr op e1 e2))

typeBExpr :: Env -> BinOp -> Expr -> Expr -> Either Error TExpr
typeBExpr env Cup e1 e2 = checkBExpr env Cup e1 e2 [((SBB,SBB),SBB)]
typeBExpr env Cap e1 e2 = checkBExpr env Cap e1 e2 [((SBB,SBB),SBB),((I,I),I)]
typeBExpr env Eq e1 e2 = checkBExpr env Eq e1 e2 [((BB,BB),B),((I,I),B),((Q,Q),B)]
typeBExpr env Lt e1 e2 = checkBExpr env Lt e1 e2 [((I,I),B),((Q,Q),B)]
typeBExpr env Gt e1 e2 = checkBExpr env Gt e1 e2 [((I,I),B),((Q,Q),B)]
typeBExpr env Equiv e1 e2 = checkBExpr env Equiv e1 e2 [((BB,BB),B),((I,I),B)]
typeBExpr env Subset e1 e2 = checkBExpr env Subset e1 e2 [((BB,BB),B),((I,I),B)]
typeBExpr env Supset e1 e2 = checkBExpr env Supset e1 e2 [((BB,BB),B),((I,I),B)]
typeBExpr env Subseteq e1 e2 = checkBExpr env Subseteq e1 e2 [((BB,BB),B),((I,I),B)]
typeBExpr env Supseteq e1 e2 = checkBExpr env Supseteq e1 e2 [((BB,BB),B),((I,I),B)]
typeBExpr env And e1 e2 = checkBExpr env And e1 e2 [((B,B),B)]
typeBExpr env Or e1 e2 = checkBExpr env Or e1 e2 [((B,B),B)]

typeUExpr :: Env -> UnOp -> Expr -> Either Error TExpr
typeUExpr env Not e = checkUExpr env Not e [(B,B)]

typeQExpr :: Env -> (String -> TExpr -> TExpr -> TExpr) -> String -> Expr -> Expr -> Either Error TExpr
typeQExpr env@(vEnv,fEnv) q x set body = do
    tset <- typeExpr env set
    let extEnv = (M.insert x BB vEnv, fEnv)
    tbody <- typeExpr extEnv body
    let pty = (typeOfTExpr tset, typeOfTExpr tbody)
    if pty == (SBB,B) then Right (q x tset tbody) else Left (TypeError (Forall x set body))

typeRUFunc :: Env -> ([TExpr] -> TExpr) -> Type -> Expr -> Either Error TExpr
typeRUFunc env con ty e = do
    te <- typeExpr env e
    if typeOfTExpr te == ty then Right (con [te]) else Left (TypeError (RFunc W [e]))

typeRBFunc :: Env -> ([TExpr] -> TExpr) -> (Type,Type) -> Expr -> Expr -> Either Error TExpr
typeRBFunc env con pty e1 e2 = do
    te1 <- typeExpr env e1
    te2 <- typeExpr env e2
    let (ty1,ty2) = (typeOfTExpr te1, typeOfTExpr te2)
    if (ty1,ty2) == pty then Right (con [te1,te2]) else Left (TypeError (RFunc RAT [e1,e2]))

typeRFunc :: Env -> Res -> [Expr] -> Either Error TExpr
typeRFunc env RAT [e1,e2] = typeRBFunc env (TRFunc RAT) (SBB,SBB) e1 e2
typeRFunc env W [e]       = typeRUFunc env (TRFunc W) I e
typeRFunc env r [e]       = typeRUFunc env (TRFunc r) BB e
typeRFunc _ r _           = Left (ArgsError (show r))

typeExpr :: Env -> Expr -> Either Error TExpr
typeExpr _ (Val n) = Right (TVal n)
typeExpr (vEnv,_) (Var x) = case M.lookup x vEnv of
    Just ty -> Right (TVar x ty)
    _       -> Left (VarError x)
typeExpr env (BExpr op e1 e2) = typeBExpr env op e1 e2
typeExpr env (UExpr op e) = typeUExpr env op e
typeExpr env (Forall x set body) = typeQExpr env TForall x set body
typeExpr env (Exists x set body) = typeQExpr env TExists x set body
typeExpr env@(_,fEnv) (Func f es) = case M.lookup f fEnv of
    Just ty@(FT tys _) -> do
        tes <- mapM (typeExpr env) es
        let aTys = [typeOfTExpr te | te <- tes]
        if tys == aTys then Right (TFunc f tes ty) else Left (TypeError (Func f es))
    _       -> Left (VarError f)
typeExpr env (RFunc r es) = typeRFunc env r es

envByExFunc :: ExFunc -> FEnv
envByExFunc (EF f tys ty) = M.singleton f (FT tys ty)

envByExFuncBlock :: ExFuncBlock -> Either Error FEnv
envByExFuncBlock (EFB efs) = Right (M.unions [envByExFunc ef | ef <- efs])

typeSCond :: Env -> SCond -> Either Error TSCond
typeSCond _ (SC None) = Right (TSC TNone)
typeSCond env (SC (CND e)) = do
    te <- typeExpr env e
    res <- if typeOfTExpr te == B then Right te else Left (TypeError e)
    return (TSC (TCND res))

extendByLetExpr :: Env -> LetExpr -> Either Error Env
extendByLetExpr env@(vEnv,fEnv) (LE x ty e) = do
    te <- typeExpr env e
    let nenv = (M.insert x ty vEnv, fEnv)
    if typeOfTExpr te == ty then Right nenv else Left (TypeError e)

extendByLetDef :: Env -> LetDef -> Either Error Env
extendByLetDef env (LD les) = foldM extendByLetExpr env les

typeLetExpr :: Env -> LetExpr -> Either Error TLetExpr
typeLetExpr env (LE x ty e) = do
    te <- typeExpr env e
    return (TLE x ty te)

typeLetDef :: Env -> LetDef -> Either Error TLetDef
typeLetDef env (LD les) = do
    tlds <- sequence [typeLetExpr env le | le <- les]
    return (TLD tlds)

typeCase :: Env -> Case -> Either Error TCase
typeCase env (Case label (ld,e)) = do
    tld <- typeLetDef env ld
    extEnv <- extendByLetDef env ld
    te <- typeExpr extEnv e
    if typeOfTExpr te == B then Right (TCase label (tld,te)) else Left (TypeError e)

typeSpec :: Spec -> Either Error TSpec
typeSpec (Spec ef sc cs) = do
    fEnv <- envByExFuncBlock ef
    let env = (M.empty,fEnv)
    tsc <- typeSCond env sc
    tcs <- mapM (typeCase env) cs
    return (TSpec tsc tcs)

showTUExpr :: UnOp -> TExpr -> Type -> String
showTUExpr Not e _ = "EXP_not (" ++ show e ++ ")"

showTBExpr :: BinOp -> TExpr -> TExpr -> Type -> String
showTBExpr Cup te1 te2 ty = "EXP_SBBunion (" ++ show te1 ++ ") (" ++ show te2 ++ ")"
showTBExpr Cap te1 te2 ty = "EXP_" ++ show ty ++ "intersection (" ++ show te1 ++ ") (" ++ show te2 ++ ")"
showTBExpr Eq te1 te2 ty = "EXP_" ++ show (typeOfTExpr te1) ++ "eq (" ++ show te1 ++ ") (" ++ show te2 ++ ")"
showTBExpr Lt te1 te2 ty = "EXP_" ++ show (typeOfTExpr te1) ++ "lt (" ++ show te1 ++ ") (" ++ show te2 ++ ")"
showTBExpr Gt te1 te2 ty = "EXP_" ++ show (typeOfTExpr te1) ++ "gt (" ++ show te1 ++ ") (" ++ show te2 ++ ")"
showTBExpr Equiv te1 te2 ty = "EXP_" ++ show (typeOfTExpr te1) ++ "overlap (" ++ show te1 ++ ") (" ++ show te2 ++ ")"
showTBExpr Subset te1 te2 ty = "EXP_" ++ show (typeOfTExpr te1) ++ "subset (" ++ show te1 ++ ") (" ++ show te2 ++ ")"
showTBExpr Supset te1 te2 ty = "EXP_" ++ show (typeOfTExpr te1) ++ "supset (" ++ show te1 ++ ") (" ++ show te2 ++ ")"
showTBExpr Subseteq te1 te2 ty = "EXP_" ++ show (typeOfTExpr te1) ++ "subseteq (" ++ show te1 ++ ") (" ++ show te2 ++ ")"
showTBExpr Supseteq te1 te2 ty = "EXP_" ++ show (typeOfTExpr te1) ++ "supseteq (" ++ show te1 ++ ") (" ++ show te2 ++ ")"
showTBExpr And te1 te2 _ = "EXP_and (" ++ show te1 ++ ") (" ++ show te2 ++ ")"
showTBExpr Or te1 te2 _ = "EXP_or (" ++ show te1 ++ ") (" ++ show te2 ++ ")"

instance Show TExpr where
    show (TVar x ty)   = "EXP_" ++ show ty ++ "var " ++ ushow x
    show (TFunc f _ (FT _ ty)) = "EXP_" ++ show ty ++ "var " ++ ushow f
    show (TVal n)    = "EXP_Q " ++ show n
    show (TUExpr op te typ) = showTUExpr op te typ
    show (TBExpr op te1 te2 typ) = showTBExpr op te1 te2 typ
    show (TForall x set body) = "EXP_forall " ++ ushow x ++ " (" ++ show set ++ ") (" ++ show body ++ ")"
    show (TExists x set body) = "EXP_exists " ++ ushow x ++ " (" ++ show set ++ ") (" ++ show body ++ ")"
    show (TRFunc r tes) = "EXP_" ++ show r ++ intercalate " " ["(" ++ show te ++ ")" | te <- tes]

instance Show TCond where
    show TNone    = "CND_None"
    show (TCND e) = "CND (" ++ show e ++ ")"

instance Show TSCond where
    show (TSC c) = show c

instance Show TLetExpr where
    show (TLE x ty e) = "DEF_" ++ show ty ++ " " ++ ushow x ++ " (" ++ show e ++ ")"

instance Show TLetDef where
    show (TLD ls) = "[" ++ intercalate "\n  ;" [show l | l <- ls] ++ "]"

instance Show TCase where
    show (TCase label (ld,e)) = "(" ++ ushow label ++ "\n ," ++ show ld ++ "\n ," ++ show e ++ ")"

instance Show TSpec where
    show (TSpec condb caseb) = "(" ++ show condb ++ "\n," ++ showcases ++ ")"
      where
        showcases = "[" ++ intercalate "\n ;\n " [show c | c <- caseb] ++ "]"

make :: String -> TSpec -> String
make n sp = initStatement ++ name ++ show sp ++ "."
  where
    initStatement = "Require Import List String QArith.\nRequire Import BBSL.BBSL BBSL.Interval BBSL.BB.\nImport ListNotations.\n\nLocal Open Scope string_scope.\nLocal Open Scope BBSL_scope.\n\nModule Export M := BBSL.M.\n\n"
    name = "Definition " ++ n ++ " : Spec :=\n"
