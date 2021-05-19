import           System.Environment (getArgs)
import           System.Exit        (exitFailure)

import           Data.List          (find, nub)
import           Data.Map           (Map)
import qualified Data.Map           as Map

import           AbsCPP
import           ErrM
import           LexCPP
import           ParCPP
import           PrintCPP


------------- Type definitions -------------

type Struct = [(Id,Type)]
type Func = ([Type], Type)
type CFunc = (Id, Entry)

data Entry = Var Type | Func Func deriving Show


type Env = ([Map Id Entry], Map Id Struct)

------------- Variables --------------------

currFuncIdent :: Id
currFuncIdent = Id "__currFunc"

------------- Main functions -------------

process :: String -> IO ()
process s = case pProgram (myLexer s) of
            Bad err  -> do putStrLn "SYNTAX ERROR"
                           putStrLn err
                           exitFailure
            Ok  tree -> case typecheck tree of
                        Bad err -> do putStrLn "TYPE ERROR"
                                      putStrLn err
                                      exitFailure
                        Ok _ -> putStrLn "OK"

main :: IO ()
main = do args <- getArgs
          case args of
            [file] -> readFile file >>= process
            _      -> getContents >>= process

typecheck :: Program -> Err ()
typecheck (PDefs defs) = do
    env2 <- addDefs emptyEnv defs
    checkDefs env2 defs
    return ()

-- First traversal of abstract syntax tree:
-- Add all structs and functions to the environment, only check for duplicate definitions and duplicate fields in struct

addDefs :: Env -> [Def] -> Err Env
addDefs env [] = Ok env
addDefs env (def:xs) = do 
    env2 <- addDef env def
    addDefs env2 xs

addDef :: Env -> Def -> Err Env
addDef env (DFun t id args stms) = updateEnv env id $ Func (map extractType args, t)
addDef (env, struct) (DStruct (Id id) fields) =
    if Map.member (Id id) struct then
        Bad $ "Can't initialize two structs with the same name: " ++ id
    else insertStruct (env, struct) (Id id) fields

insertStruct :: Env -> Id -> [Field] -> Err Env
insertStruct (env, struct) id fields =
    if length (nub ids) /= length ids then
        Bad "Duplicate variable occurrence in struct"
    else Ok $ (env, Map.insert id [(ident, t) | (FDecl t ident) <- fields] struct)
    where ids = [ident | (FDecl t ident) <- fields]

-- Second traversal of abstract syntax tree:
-- Typecheck all of the program

checkDefs :: Env -> [Def] -> Err Env
checkDefs env [] = Ok env
checkDefs env (def:xs) = do
    env2 <- checkDef env def 
    checkDefs env2 xs

checkDef :: Env -> Def -> Err Env
checkDef env (DFun t id args stms) = do
    checkTypesDef env [t]
    env2 <- updateEnv (newBlock env) currFuncIdent $ Func (map extractType args, t)
    env3 <- checkArgs env2 args
    checkStms env3 stms
checkDef env (DStruct id fields) = checkStruct env id fields

checkStruct :: Env -> Id -> [Field] -> Err Env
checkStruct (env, struct) id fields = do
    checkTypesDefV (env, struct) types
    return (env, struct)
    where types = [t | (FDecl t ident) <- fields]

checkArgs :: Env -> [Arg] -> Err Env
checkArgs env []       = Ok env
checkArgs env (arg:xs) = do
    env2 <- checkArg env arg
    checkArgs env2 xs

checkArg :: Env -> Arg -> Err Env
checkArg env (ADecl t id) = do 
    checkTypesDefV env [t]
    updateEnv env id $ Var t

checkStms :: Env -> [Stm] -> Err Env
checkStms env [] = Ok $ deleteBlock env
checkStms env (stm:xs) = do
    env2 <- checkStm env stm 
    checkStms env2 xs

checkStm :: Env -> Stm -> Err Env
checkStm env (SExp exp) = do
    inferExp env exp
    return env
    
checkStm env (SDecls t idins) = checkIdins env t idins

checkStm env (SReturn exp) = case lookupEnv env currFuncIdent of
    Ok (Var typ) -> Bad ""
    Ok (Func (args, ret)) -> do
        checkExp env exp ret
        return env
    Bad err -> Bad err

checkStm env SReturnV = case lookupEnv env currFuncIdent of
    Ok (Var typ) -> Bad ""
    Ok (Func (args, ret)) ->
        if ret == Type_void 
            then Ok env
        else Bad $ "return-statement without a value, in function returning '" ++ printTree ret
    Bad err -> Bad err

checkStm env (SWhile exp stm) = do
   checkExp env exp Type_bool
   checkStm env stm

checkStm env (SDoWhile stm exp) = do
   checkExp env exp Type_bool
   checkStm env stm

checkStm env (SFor exp1 exp2 exp3 stm) = do
   inferExp env exp1
   checkExp env exp2 Type_bool
   inferExp env exp3
   checkStm env stm

checkStm env (SBlock stms) = checkStms (newBlock env) stms

checkStm env (SIfElse exp stm1 stm2) = do
   checkExp env exp Type_bool
   checkStm env stm1
   checkStm env stm2

checkIdins :: Env -> Type -> [IdIn] -> Err Env
checkIdins env _ []        = Ok env
checkIdins env t (idin:xs) = do
    env2 <- checkIdin env t idin
    checkIdins env2 t xs

checkIdin :: Env -> Type -> IdIn -> Err Env
checkIdin env t (IdNoInit id) = do
    checkTypesDefV env [t]
    updateEnv env id $ Var t
checkIdin env t (IdInit id exp) = do 
    checkTypesDefV env [t]
    checkExp env exp t
    updateEnv env id $ Var t

checkExps :: Env -> [Exp]-> [Type] -> Err ()
checkExps env [] [] = Ok ()
checkExps env (exp:xs) (t:ys) = do
    checkExp env exp t
    checkExps env xs ys

checkExp :: Env -> Exp -> Type -> Err Type
checkExp env exp t = do
    t2 <- inferExp env exp
    if t == t2 || t == Type_double && t2 == Type_int
        then Ok t
    else Bad $ "Expected: " ++ (show t) ++ ", but received: " ++ (show t2)

inferExp :: Env -> Exp -> Err Type
inferExp env ETrue            = Ok Type_bool
inferExp env EFalse           = Ok Type_bool
inferExp env (EInt int)       = Ok Type_int
inferExp env (EDouble double) = Ok Type_double

inferExp env (EId (Id id)) = case lookupEnv env (Id id) of
   Bad err     -> Bad err
   Ok (Func _) -> Bad $ id ++ " is not a variable"
   Ok (Var t)  -> Ok t

inferExp ((env:xs), struct) (EApp (Id id) exps) = case lookupEnv (xs, struct) (Id id) of
    Bad err               -> Bad err
    Ok (Var _)            -> Bad $ id ++ " is not a function"
    Ok (Func (args, ret)) ->
        if length args /= length exps then
            Bad $ "Expected " ++ (show $ length args) ++ " arguments, but received " ++ (show $ length exps) ++ " instead"
        else do
            checkExps ((env:xs), struct) exps args
            return ret

inferExp env (EProj exp (Id id)) = case inferExp env exp of
    Bad err              -> Bad err
    Ok (TypeId (Id tid)) -> case lookupTypeId env (Id tid) of
        Bad err   -> Bad err
        Ok struct -> case find (\(ident, typ) -> ident == (Id id)) struct of
            Just (ident, typ) -> Ok typ
            Nothing           -> Bad $ "Struct " ++ tid ++ " doesn't have property with name " ++ id
    Ok t                 -> Bad $ "Can't access property of a primitve type " ++ show t

inferExp env (EPIncr exp) = inferIncrDecr env exp
inferExp env (EPDecr exp) = inferIncrDecr env exp
inferExp env (EIncr exp)  = inferIncrDecr env exp
inferExp env (EDecr exp)  = inferIncrDecr env exp

inferExp env (EUPlus exp)  = inferUnary env exp
inferExp env (EUMinus exp) =  inferUnary env exp

inferExp env (ETimes exp1 exp2) = inferArithm env exp1 exp2
inferExp env (EDiv exp1 exp2)   = inferArithm env exp1 exp2
inferExp env (EPlus exp1 exp2)  = Bad "TODO"
inferExp env (EMinus exp1 exp2) = inferArithm env exp1 exp2

inferExp env (ETwc exp1 exp2) = inferComp env exp1 exp2 Type_int

inferExp env (ELt exp1 exp2)   = Bad "TODO"
inferExp env (EGt exp1 exp2)   = inferComp env exp1 exp2 Type_bool
inferExp env (ELtEq exp1 exp2) = inferComp env exp1 exp2 Type_bool
inferExp env (EGtEq exp1 exp2) = inferComp env exp1 exp2 Type_bool

inferExp env (EEq exp1 exp2)  = inferEqual env exp1 exp2
inferExp env (ENEq exp1 exp2) = inferEqual env exp1 exp2

inferExp env (EAnd exp1 exp2) = inferConDis env exp1 exp2
inferExp env (EOr exp1 exp2)  = inferConDis env exp1 exp2

inferExp env (EAss exp1 exp2) = do 
    checkVarOrProj exp1
    typ1 <- inferExp env exp1
    checkExp env exp2 typ1

inferExp env (ECond exp1 exp2 exp3) = do
    checkExp env exp1 Type_bool
    typ2 <- inferExp env exp2
    typ3 <- inferExp env exp3
    checkTypesDef env [typ2, typ3]
    implTypeConv typ2 typ3

inferIncrDecr :: Env -> Exp -> Err Type
inferIncrDecr env exp = do
    checkVarOrProj exp
    typ <- inferExp env exp
    checkNum typ
    return typ

inferUnary :: Env -> Exp -> Err Type
inferUnary env exp = do
    typ <- inferExp env exp
    checkNum typ
    return typ

inferArithm :: Env -> Exp -> Exp -> Err Type
inferArithm env exp1 exp2 = do
    typ1 <- inferExp env exp1
    typ2 <- inferExp env exp2
    checkNum typ1
    checkNum typ2
    implTypeConv typ1 typ2

inferComp :: Env -> Exp -> Exp -> Type -> Err Type
inferComp env exp1 exp2 typ = do
    typ1 <- inferExp env exp1
    typ2 <- inferExp env exp2
    checkNum typ1
    checkNum typ2
    implTypeConv typ1 typ2
    return typ

inferEqual :: Env -> Exp -> Exp -> Err Type
inferEqual env exp1 exp2 = do
    typ1 <- inferExp env exp1
    typ2 <- inferExp env exp2
    checkTypesDef env [typ1, typ2]
    return Type_bool

inferConDis :: Env -> Exp -> Exp -> Err Type
inferConDis env exp1 exp2 = do
    checkExps env [exp1, exp2] [Type_bool, Type_bool]
    return Type_bool

checkNum :: Type -> Err Type
checkNum t
    | t `elem` [Type_int, Type_double] = Ok t
    | otherwise = Bad "Operation not available on non-number type"

checkVarOrProj :: Exp -> Err ()
checkVarOrProj (EId id) = Ok ()
checkVarOrProj (EProj exp id) = Ok ()
checkVarOrProj _ = Bad $ "Can't perform operation on complex expression"

implTypeConv :: Type -> Type -> Err Type
implTypeConv typ1 typ2
    | typ1 == typ2 = Ok typ1
    | ((typ1 == Type_double && typ2 == Type_int) || (typ2 == Type_double && typ1 == Type_int))  = Ok Type_double
    | otherwise = Bad $ "Expressions not of the same type: " ++ show typ1 ++ " and " ++ show typ2

------------- Auxiliary functions -------------

checkTypesDef :: Env -> [Type] -> Err ()
checkTypesDef env [] = Ok ()
checkTypesDef env ((TypeId id):xs) = do
    lookupTypeId env id
    return ()
checkTypesDef env (t:xs) = checkTypesDef env xs

checkTypesDefV :: Env -> [Type] -> Err ()
checkTypesDefV env (Type_void:xs) = Bad "Type void not allowed"
checkTypesDefV env types = checkTypesDef env types

extractType :: Arg -> Type
extractType (ADecl t _) = t

lookupTypeId :: Env -> Id -> Err Struct
lookupTypeId (env, struct) (Id id) =
    case Map.lookup (Id id) struct of
        Just entry -> Ok entry
        Nothing    -> Bad $ "Type not defined: " ++ id

lookupEnv :: Env -> Id -> Err Entry
lookupEnv ([], _) (Id id) = Bad $ id ++ " undefined"
lookupEnv ((x:xs), struct) id  = case Map.lookup id x of
    Just entry -> Ok entry
    Nothing    -> lookupEnv (xs, struct) id

updateEnv :: Env -> Id -> Entry -> Err Env
updateEnv ((x:xs), struct) (Id id) entry =
    if Map.member (Id id) x then
        Bad $ "Variable " ++ id ++ " already declared in this block"
    else Ok $ (Map.insert (Id id) entry x :xs, struct)

-- Building the stack from front to back. The first element of the list is always the top element of the stack.
newBlock :: Env -> Env
newBlock (env, struct) = (Map.empty:env, struct)

deleteBlock :: Env -> Env
deleteBlock ((env:xs), struct) = (xs, struct)

emptyEnv :: Env
emptyEnv = ([Map.empty], Map.empty)
