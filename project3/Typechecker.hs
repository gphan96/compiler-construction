module Typechecker where

import           AbsCPP
import           ErrM
import           LexCPP
import           ParCPP
import           PrintCPP
import qualified TypedAST as TA

import           Data.List          (find, nub)
import           Data.Map           (Map)
import qualified Data.Map           as Map


------------- Type definitions -------------

type Struct = [(Id,Type)]
type Func = ([Type], Type)

data Entry = Var Type | Func Func deriving Show


type Env = ([Map Id Entry], Map Id Struct)

------------- Variables --------------------

currFuncIdent :: Id
currFuncIdent = Id "__currFunc"

------------- Main functions ---------------

typecheck :: Program -> Err (TA.ProgramT, [(Id, [(Id, Type)])])
typecheck (PDefs defs) = do
    env2 <- addDefs emptyEnv defs
    ((env3, structs), defts) <- checkDefs env2 defs []
    return $ (TA.PDefs defts, Map.assocs structs)

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

checkDefs :: Env -> [Def] -> [TA.DefT] -> Err (Env, [TA.DefT])
checkDefs env [] deft = Ok (env, deft)
checkDefs env (def:xs) defts = do
    (env2, deft) <- checkDef env def
    checkDefs env2 xs $ defts ++ [deft]

checkDef :: Env -> Def -> Err (Env, TA.DefT)
checkDef env (DFun t id args stms) = do
    checkTypesDef env [t]
    env2 <- updateEnv (newBlock env) currFuncIdent $ Func (map extractType args, t)
    env3 <- checkArgs env2 args
    (env4, stmst) <- checkStms env3 stms []
    return (env4, (TA.DFun t id args stmst))
checkDef env (DStruct id fields) = do
    env <- checkStruct env id fields
    return (env, (TA.DStruct id fields))

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

checkStms :: Env -> [Stm] -> [TA.StmT] -> Err (Env, [TA.StmT])
checkStms env [] stmst = Ok $ (deleteBlock env, stmst)
checkStms env (stm:xs) stmst = do
    (env2, stmt) <- checkStm env stm 
    checkStms env2 xs $ stmst ++ [stmt]

checkStm :: Env -> Stm -> Err (Env, TA.StmT)
checkStm env (SExp exp) = do
    (typ, expt) <- inferExp env exp
    return (env, (TA.SExp expt))
    
checkStm env (SDecls t idins) = do 
    (env2, idinst) <- checkIdins env t idins []
    return (env2, TA.SDecls t idinst)

checkStm env (SReturn exp) = case lookupEnv env currFuncIdent of
    Ok (Var typ) -> Bad ""
    Ok (Func (args, ret)) -> do
        (typ2, expt) <- checkExp env exp ret
        return (env, (TA.SReturn expt))
    Bad err -> Bad err

checkStm env SReturnV = case lookupEnv env currFuncIdent of
    Ok (Var typ) -> Bad ""
    Ok (Func (args, ret)) ->
        if ret == Type_void 
            then Ok (env, TA.SReturnV)
        else Bad $ "return-statement without a value, in function returning '" ++ printTree ret
    Bad err -> Bad err

checkStm env (SWhile exp stm) = do
   (typ2, expt) <- checkExp env exp Type_bool
   (env2, stmt) <- checkStm env stm
   return (env2, TA.SWhile expt stmt)

checkStm env (SDoWhile stm exp) = do
   (typ2, expt) <- checkExp env exp Type_bool
   (env2, stmt) <- checkStm env stm
   return (env2, TA.SDoWhile stmt expt)

checkStm env (SFor exp1 exp2 exp3 stm) = do
   (typ1, expt1) <- inferExp env exp1
   (typ2, expt2) <- checkExp env exp2 Type_bool
   (typ3, expt3) <- inferExp env exp3
   (env2, stmt) <- checkStm env stm
   return (env2, TA.SFor expt1 expt2 expt3 stmt)

checkStm env (SBlock stms) = do
    (env2, stmst) <- checkStms (newBlock env) stms []
    return (env2, TA.SBlock stmst)

checkStm env (SIfElse exp stm1 stm2) = do
   (typ1, expt) <- checkExp env exp Type_bool
   (env2, stmt1) <- checkStm env stm1
   (env3, stmt2) <- checkStm env2 stm2 -- maybe use env instead of env2 here
   return (env3, TA.SIfElse expt stmt1 stmt2)

checkIdins :: Env -> Type -> [IdIn] -> [TA.IdInT] -> Err (Env, [TA.IdInT])
checkIdins env _ [] idinst        = Ok (env, idinst)
checkIdins env t (idin:xs) idinst = do
    (env2, idint) <- checkIdin env t idin
    checkIdins env2 t xs $ idinst ++ [idint]

checkIdin :: Env -> Type -> IdIn -> Err (Env, TA.IdInT)
checkIdin env t (IdNoInit id) = do
    checkTypesDefV env [t]
    env2 <- updateEnv env id $ Var t
    return (env2, (TA.IdNoInit id))
checkIdin env t (IdInit id exp) = do 
    checkTypesDefV env [t]
    (typ1, expt) <- checkExp env exp t
    env2 <- updateEnv env id $ Var t
    return (env2, (TA.IdInit id expt))

checkExps :: Env -> [Exp]-> [Type] -> [TA.ExpT] -> Err [TA.ExpT]
checkExps env [] [] expst = Ok expst
checkExps env (exp:xs) (t:ys) expst = do
    (typ1, expt) <- checkExp env exp t
    checkExps env xs ys $  expst ++ [expt]

checkExp :: Env -> Exp -> Type -> Err (Type, TA.ExpT)
checkExp env exp t = do
    (t2, (e, t3)) <- inferExp env exp
    if t == t2 || t == Type_double && t2 == Type_int
        then Ok (t, (e, t))
    else Bad $ "Expected: " ++ (show t) ++ ", but received: " ++ (show t2)

inferExp :: Env -> Exp -> Err (Type, TA.ExpT)
inferExp env ETrue            = Ok (Type_bool, (TA.ETrue, Type_bool))
inferExp env EFalse           = Ok (Type_bool, (TA.EFalse, Type_bool))
inferExp env (EInt int)       = Ok (Type_int, ((TA.EInt int), Type_int))
inferExp env (EDouble double) = Ok (Type_double, ((TA.EDouble double), Type_double))

inferExp env (EId (Id id)) = case lookupEnv env (Id id) of
   Bad err     -> Bad err
   Ok (Func _) -> Bad $ id ++ " is not a variable"
   Ok (Var t)  -> Ok (t, (TA.EId (Id id), t))

inferExp ((env:xs), struct) (EApp (Id id) exps) = case lookupEnv (xs, struct) (Id id) of
    Bad err               -> Bad err
    Ok (Var _)            -> Bad $ id ++ " is not a function"
    Ok (Func (args, ret)) ->
        if length args /= length exps then
            Bad $ "Expected " ++ (show $ length args) ++ " arguments, but received " ++ (show $ length exps) ++ " instead"
        else do
            expst <- checkExps ((env:xs), struct) exps args []
            return (ret, ((TA.EApp (Id id) expst), ret))

inferExp env (EProj exp (Id id)) = case inferExp env exp of
    Bad err              -> Bad err
    Ok ((TypeId (Id tid)), expt) -> case lookupTypeId env (Id tid) of
        Bad err   -> Bad err
        Ok struct -> case find (\(ident, typ) -> ident == (Id id)) struct of
            Just (ident, typ) -> Ok (typ, ((TA.EProj expt (Id id)), typ))
            Nothing           -> Bad $ "Struct " ++ tid ++ " doesn't have property with name " ++ id
    Ok t                 -> Bad $ "Can't access property of a primitve type " ++ show t

inferExp env (EPIncr exp) = do
    (typ1, expt) <- inferIncrDecr env exp
    return (typ1, ((TA.EPIncr expt), typ1))
inferExp env (EPDecr exp) = do
    (typ1, expt) <- inferIncrDecr env exp
    return (typ1, ((TA.EPDecr expt), typ1))
inferExp env (EIncr exp)  = do
    (typ1, expt) <- inferIncrDecr env exp
    return (typ1, ((TA.EIncr expt), typ1))
inferExp env (EDecr exp)  = do
    (typ1, expt) <- inferIncrDecr env exp
    return (typ1, ((TA.EDecr expt), typ1))

inferExp env (EUPlus exp)  = do
    (typ1, expt) <- inferUnary env exp
    return (typ1, ((TA.EUPlus expt), typ1))
inferExp env (EUMinus exp) = do
    (typ1, expt) <- inferUnary env exp
    return (typ1, ((TA.EUMinus expt), typ1))

inferExp env (ETimes exp1 exp2) = do
    (typ, expt1, expt2) <- inferArithm env exp1 exp2
    return (typ, ((TA.ETimes expt1 expt2), typ))
inferExp env (EDiv exp1 exp2)   = do
    (typ, expt1, expt2) <- inferArithm env exp1 exp2
    return (typ, ((TA.EDiv expt1 expt2), typ))
inferExp env (EPlus exp1 exp2)  = do
    (typ, expt1, expt2) <- inferArithm env exp1 exp2
    return (typ, ((TA.EPlus expt1 expt2), typ))
inferExp env (EMinus exp1 exp2) = do
    (typ, expt1, expt2) <- inferArithm env exp1 exp2
    return (typ, ((TA.EMinus expt1 expt2), typ))

inferExp env (ETwc exp1 exp2) = do
    (typ, expt1, expt2) <- inferComp env exp1 exp2 Type_int
    return (typ, ((TA.ETwc expt1 expt2), typ))

inferExp env (ELt exp1 exp2)   = do
    (typ, expt1, expt2) <- inferComp env exp1 exp2 Type_bool
    return (typ, ((TA.ELt expt1 expt2), typ))
inferExp env (EGt exp1 exp2)   = do
    (typ, expt1, expt2) <- inferComp env exp1 exp2 Type_bool
    return (typ, ((TA.EGt expt1 expt2), typ))
inferExp env (ELtEq exp1 exp2) = do
    (typ, expt1, expt2) <- inferComp env exp1 exp2 Type_bool
    return (typ, ((TA.ELtEq expt1 expt2), typ))
inferExp env (EGtEq exp1 exp2) = do
    (typ, expt1, expt2) <- inferComp env exp1 exp2 Type_bool
    return (typ, ((TA.EGtEq expt1 expt2), typ))

inferExp env (EEq exp1 exp2)  = do
    (typ, expt1, expt2) <- inferEqual env exp1 exp2
    return (typ, ((TA.EEq expt1 expt2), typ))
inferExp env (ENEq exp1 exp2) = do
    (typ, expt1, expt2) <- inferEqual env exp1 exp2
    return (typ, ((TA.ENEq expt1 expt2), typ))

inferExp env (EAnd exp1 exp2) = do
    (typ, expt1, expt2) <- inferConDis env exp1 exp2
    return (typ, ((TA.EAnd expt1 expt2), typ))
inferExp env (EOr exp1 exp2)  = do
    (typ, expt1, expt2) <- inferConDis env exp1 exp2
    return (typ, ((TA.EOr expt1 expt2), typ))

inferExp env (EAss exp1 exp2) = do 
    checkVarOrProj exp1
    (typ1, expt1) <- inferExp env exp1
    (typ2, expt2) <- checkExp env exp2 typ1
    return (typ2, ((TA.EAss expt1 expt2), typ2))

inferExp env (ECond exp1 exp2 exp3) = do
    (typ1, expt1) <- checkExp env exp1 Type_bool
    (typ2, expt2) <- inferExp env exp2
    (typ3, expt3) <- inferExp env exp3
    checkTypesDef env [typ2, typ3]
    typ4 <- implTypeConv typ2 typ3
    return (typ4, ((TA.ECond expt1 expt2 expt3), typ4))

inferIncrDecr :: Env -> Exp -> Err (Type, TA.ExpT)
inferIncrDecr env exp = do
    checkVarOrProj exp
    (typ, expt) <- inferExp env exp
    checkNum typ
    return (typ, expt)

inferUnary :: Env -> Exp -> Err (Type, TA.ExpT)
inferUnary env exp = do
    (typ, expt) <- inferExp env exp
    checkNum typ
    return (typ, expt)

inferArithm :: Env -> Exp -> Exp -> Err (Type, TA.ExpT, TA.ExpT)
inferArithm env exp1 exp2 = do
    (typ1, expt1) <- inferExp env exp1
    (typ2, expt2) <- inferExp env exp2
    checkNum typ1
    checkNum typ2
    typ3 <- implTypeConv typ1 typ2
    return (typ3, expt1, expt2)

inferComp :: Env -> Exp -> Exp -> Type -> Err (Type, TA.ExpT, TA.ExpT)
inferComp env exp1 exp2 typ = do
    (typ1, expt1) <- inferExp env exp1
    (typ2, expt2) <- inferExp env exp2
    checkNum typ1
    checkNum typ2
    implTypeConv typ1 typ2
    return (typ, expt1, expt2)

inferEqual :: Env -> Exp -> Exp -> Err (Type, TA.ExpT, TA.ExpT)
inferEqual env exp1 exp2 = do
    (typ1, expt1) <- inferExp env exp1
    (typ2, expt2) <- inferExp env exp2
    checkTypesDef env [typ1, typ2]
    return (Type_bool, expt1, expt2)

inferConDis :: Env -> Exp -> Exp -> Err (Type, TA.ExpT, TA.ExpT)
inferConDis env exp1 exp2 = do
    expst <- checkExps env [exp1, exp2] [Type_bool, Type_bool] []
    return (Type_bool, expst !! 0, expst !! 1)

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
