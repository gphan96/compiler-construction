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
type CFunc =  (Id, Entry)

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

typecheck :: Program -> Err () --main typecheck function
typecheck (PDefs defs) = case addDefs emptyEnv defs of
   Bad err -> Bad err
   Ok env2 -> case checkDefs env2 defs of
      Bad err -> Bad err
      Ok _    -> Ok ()

addDefs :: Env -> [Def] -> Err Env
addDefs env [] = Ok env
addDefs env (def:xs) = case addDef env def of
   Bad err -> Bad err
   Ok env2 -> addDefs env2 xs

addDef :: Env -> Def -> Err Env
addDef env (DFun t id args stms) = updateEnv env id $ Func (map extractType args, t)
addDef (env, struct) (DStruct (Id id) fields) =
   if Map.member (Id id) struct then
      Bad $ "Can't initialize two structs with the same name: " ++ id
   else insertStruct (env, struct) (Id id) fields

checkDefs :: Env -> [Def] -> Err Env
checkDefs env [] = Ok env
checkDefs env (def:xs) = case checkDef env def of
                         Bad err -> Bad err
                         Ok env2 -> checkDefs env2 xs

checkDef :: Env -> Def -> Err Env
checkDef env (DFun t id args stms) = case checkTypesDef env [t] of
   Bad err -> Bad err
   Ok _    -> case checkArgs (insertFunct (newBlock env) id) args of
      Bad err -> Bad err
      Ok env2 -> checkStms env2 stms
checkDef env (DStruct id fields) = checkStruct env id fields

insertStruct :: Env -> Id -> [Field] -> Err Env
insertStruct (env, struct) id fields =
   if length (nub ids) /= length ids then
      Bad "Duplicate variable occurrence in struct"
   else Ok $ (env, Map.insert id [(ident, t) | (FDecl t ident) <- fields] struct)
   where ids = [ident | (FDecl t ident) <- fields]

checkStruct :: Env -> Id -> [Field] -> Err Env
checkStruct (env, struct) id fields = do
   checkTypesDefV (env, struct) types
   return (env, struct)
   where types = [t | (FDecl t ident) <- fields]

insertFunct :: Env -> Id -> Env
insertFunct ((x:xs), struct) id = (Map.insert currFuncIdent (Var (TypeId id)) x :xs, struct)

lookupFunc :: Env -> Err CFunc
lookupFunc ([], _) = Bad $ "Function specific calls can only be made inside a function"
lookupFunc env@(x:xs, struct) = case lookupEnv env currFuncIdent of
  Ok (Var (TypeId id)) -> lookupFuncDef (xs, struct) id
    where
      lookupFuncDef :: Env -> Id -> Err CFunc
      lookupFuncDef ([], _) id = Bad $ "No function with the name '" ++ show id ++ "' defined"
      lookupFuncDef env@(x:xs, struct) id = case lookupEnv env id of
        Ok (Func func) -> Ok (id, (Func func))
        Bad _          -> lookupFuncDef (xs, struct) id
  Bad _                 -> lookupFunc (xs, struct)


checkTypesDefV :: Env -> [Type] -> Err ()
checkTypesDefV env [] = Ok ()
checkTypesDefV env ((TypeId id):xs) = case lookupTypeId env id of
   Bad err -> Bad err
   Ok _    -> Ok ()
checkTypesDefV env (Type_void:xs) = Bad "Type void not allowed"
checkTypesDefV env (t:xs) = checkTypesDefV env xs

checkTypesDef :: Env -> [Type] -> Err ()
checkTypesDef env [] = Ok ()
checkTypesDef env ((TypeId id):xs) = case lookupTypeId env id of
   Bad err -> Bad err
   Ok _    -> Ok ()
checkTypesDef env (t:xs) = checkTypesDef env xs

checkArgs :: Env -> [Arg] -> Err Env
checkArgs env []       = Ok env
checkArgs env (arg:xs) = case checkArg env arg of
                         Bad err -> Bad err
                         Ok env2 -> checkArgs env2 xs

checkArg :: Env -> Arg -> Err Env
checkArg env (ADecl t id)            = case checkTypesDefV env [t] of
   Bad err -> Bad err
   Ok _    -> updateEnv env id $ Var t

checkStms :: Env -> [Stm] -> Err Env
checkStms env [] = Ok $ deleteBlock env
checkStms env (stm:xs) = case checkStm env stm of
                         Bad err -> Bad err
                         Ok env2 -> checkStms env2 xs

checkStm :: Env -> Stm -> Err Env
-- not sure for which type to check this Exp. Maybe just call inferExp and if it fails return an error ?!
checkStm env (SExp exp) = case inferExp env exp of
                          Bad err -> Bad err
                          Ok _    -> Ok env
checkStm env (SDecls t idins) = checkIdins env t idins
checkStm env (SReturn exp) = do
  let Ok (_, Func (args, ret)) = lookupFunc env
  checkExp env exp ret
  return env

checkStm env SReturnV = do
  let Ok (id, Func (args, ret)) = lookupFunc env
  if ret == Type_void then
    return env
  else  Bad $ "return-statement without a value, in function '" ++ show id ++ "' returning '" ++ printTree ret


checkStm env (SWhile exp stm) = do                         --Task 2
   checkExp env exp Type_bool
   checkStm env stm
checkStm env (SDoWhile stm exp) = do                       --Task 2
   checkExp env exp Type_bool
   checkStm env stm

checkStm env (SFor exp1 exp2 exp3 stm) = do
   inferExp env exp1
   checkExp env exp2 Type_bool
   inferExp env exp3
   checkStm env stm

checkStm env (SBlock stms) = checkStms (newBlock env) stms
checkStm env (SIfElse exp stm1 stm2) = do        --Task 2
   checkExp env exp Type_bool
   checkStm env stm1
   checkStm env stm2

checkIdins :: Env -> Type -> [IdIn] -> Err Env
checkIdins env _ []        = Ok env
checkIdins env t (idin:xs) = case checkIdin env t idin of
                             Bad err -> Bad err
                             Ok env2 -> checkIdins env2 t xs

checkIdin :: Env -> Type -> IdIn -> Err Env
checkIdin env t (IdNoInit id)   = case checkTypesDefV env [t] of
   Bad err -> Bad err
   Ok _    -> updateEnv env id $ Var t
checkIdin env t (IdInit id exp) = case checkTypesDefV env [t] of
   Bad err -> Bad err
   Ok _    -> case checkExp env exp t of
      Bad err -> Bad err
      Ok _    -> updateEnv env id $ Var t


checkExps :: Env -> [Exp]-> [Type] -> Err ()
checkExps env [] [] = Ok ()
checkExps env (exp:xs) (t:ys) = case checkExp env exp t of
                                Bad err -> Bad err
                                Ok _    -> checkExps env xs ys

checkExp :: Env -> Exp -> Type -> Err Type
checkExp env exp t = do
   t2 <- inferExp env exp
   if t == t2 || t == Type_double && t2 == Type_int
      then Ok t
   else Bad $ "Expected: " ++ (show t) ++ ", but received: " ++ (show t2)


inferExp :: Env -> Exp -> Err Type
inferExp env ETrue = Ok Type_bool
inferExp env EFalse = Ok Type_bool
inferExp env (EInt int) = Ok Type_int
inferExp env (EDouble double) = Ok Type_double
inferExp env (EId (Id id)) = case lookupEnv env (Id id) of
   Bad err     -> Bad err
   Ok (Func _) -> Bad $ id ++ " is not a variable"
   Ok (Var t)  -> Ok t
inferExp ((env:xs), struct) (EApp (Id id) exps) = case lookupEnv (xs, struct) (Id id) of
   Bad err -> Bad err
   Ok (Var _) -> Bad $ id ++ " is not a function"
   Ok (Func (args, ret)) ->
      if length args /= length exps then
         Bad $ "Expected " ++ (show $ length args) ++ " arguments, but received " ++ (show $ length exps) ++ " instead"
      else case checkExps ((env:xs), struct) exps args of
         Bad err -> Bad err
         Ok _    -> Ok ret

inferExp env (EProj exp (Id id)) = case inferExp env exp of
   Bad err        -> Bad err
   Ok (TypeId (Id tid)) -> case lookupTypeId env (Id tid) of
      Bad err   -> Bad err
      Ok struct -> case find (\(ident, typ) -> ident == (Id id)) struct of
         Just (ident, typ) -> Ok typ
         Nothing           -> Bad $ "Struct " ++ tid ++ " doesn't have property with name " ++ id
   Ok t           -> Bad $ "Can't access property of a primitve type " ++ show t

inferExp env (EPIncr exp) = findTypeNum env exp
inferExp env (EPDecr exp) = findTypeNum env exp
inferExp env (EIncr exp) = findTypeNum env exp
inferExp env (EDecr exp) = findTypeNum env exp
inferExp env (EUPlus exp) = do
   typ <- inferExp env exp
   checkNum typ
   return typ
inferExp env (EUMinus exp) = do
   typ <- inferExp env exp
   checkNum typ
   return typ

inferExp env (ETimes exp1 exp2) = do
   typ1 <- inferExp env exp1
   typ2 <- inferExp env exp2
   checkNum typ1
   checkNum typ2
   implTypeConv typ1 typ2

inferExp env (EDiv exp1 exp2) = do
   typ1 <- inferExp env exp1
   typ2 <- inferExp env exp2
   checkNum typ1
   checkNum typ2
   implTypeConv typ1 typ2

inferExp env (EPlus exp1 exp2) = do
   typ1 <- inferExp env exp1
   typ2 <- inferExp env exp2
   checkNum typ1
   checkNum typ2
   implTypeConv typ1 typ2

inferExp env (EMinus exp1 exp2) = inferArithmBin env exp1 exp2

inferExp env (ETwc exp1 exp2) = returnComparison env Type_int exp1 exp2

inferExp env (ELt exp1 exp2) = returnComparison env Type_bool exp1 exp2

inferExp env (EGt exp1 exp2) = returnComparison env Type_bool exp1 exp2
inferExp env (ELtEq exp1 exp2) = do
   typ1 <- inferExp env exp1
   typ2 <- inferExp env exp2
   checkNum typ1
   checkNum typ2
   implTypeConv typ1 typ2
   return Type_bool

inferExp env (EGtEq exp1 exp2) = returnComparison env Type_bool exp1 exp2

inferExp env (EEq exp1 exp2) = do
   typ1 <- inferExp env exp1
   typ2 <- inferExp env exp2
   checkTypesDef env [typ1, typ2]
   implTypeConv typ1 typ2
   return Type_bool

inferExp env (ENEq exp1 exp2) = do
   typ1 <- inferExp env exp1
   typ2 <- inferExp env exp2
   checkTypesDef env [typ1, typ2]
   implTypeConv typ1 typ2
   return Type_bool

inferExp env (EAnd exp1 exp2) = do
   checkExps env [exp1, exp2] [Type_bool, Type_bool]
   return Type_bool

inferExp env (EOr exp1 exp2) = do
   checkExps env [exp1, exp2] [Type_bool, Type_bool]
   return Type_bool

inferExp env (EAss exp1 exp2) = do
   checkVarOrProj exp1
   typ1 <- inferExp env exp1
   checkExp env exp2 typ1
inferExp env (ECond exp1 exp2 exp3) = do
   checkExp env exp1 Type_bool
   inferBinEq env exp2 exp3


checkNum :: Type -> Err Type
checkNum t
   | t `elem` [Type_int, Type_double] = Ok t
   | otherwise = Bad "Operation not available on non-number type"

checkVarOrProj :: Exp -> Err ()
checkVarOrProj (EId id) = Ok ()
checkVarOrProj (EProj exp id) = Ok ()
checkVarOrProj _ = Bad $ "Can't perform operation on complex expression"

inferBinEq :: Env -> Exp -> Exp -> Err Type
inferBinEq env exp1 exp2 = do
   typ1 <- inferExp env exp1
   typ2 <- inferExp env exp2
   checkTypesDef env [typ1, typ2]
   implTypeConv typ1 typ2

implTypeConv :: Type -> Type -> Err Type
implTypeConv typ1 typ2
   | typ1 == typ2 = Ok typ1
   | ((typ1 == Type_double && typ2 == Type_int) || (typ2 == Type_double && typ1 == Type_int))  = Ok Type_double
   | otherwise = Bad $ "Expressions not of the same type: " ++ show typ1 ++ " and " ++ show typ2

findTypeNum :: Env -> Exp -> Err Type
findTypeNum env exp = do
   checkVarOrProj exp
   typ <- inferExp env exp
   if typ `elem` [Type_int, Type_double]
   then return typ
   else Bad $ "Type error of expression " ++ printTree exp

inferArithmBin :: Env -> Exp -> Exp -> Err Type
inferArithmBin env exp1 exp2 =
   case implicitConv env exp1 exp2 of
      Ok typ -> return typ
      Bad _  -> do typ <- inferExp env exp1
                   case typ of
                      Type_bool -> Bad $ "Unexpected type of " ++ printTree exp1
                      _         -> Bad $ "Unexpected type of " ++ printTree exp2

returnComparison :: Env -> Type -> Exp -> Exp -> Err Type
returnComparison env r_typ exp1 exp2 =
   case implicitConv env exp1 exp2 of
      Ok _  -> return r_typ
      Bad _ -> Bad $ "Expected type 'int' or 'double' for both expression "
                     ++ printTree exp1 ++ " and " ++ printTree exp2

returnBool :: Env -> Exp -> Exp -> Err Type
returnBool env exp1 exp2 = do
   typ <- inferExp env exp1
   case typ of
      Type_bool -> do checkExp env exp2 typ
                      return typ
      _         -> Bad $ "In expression: " ++ printTree exp1
                         ++ ", expected type: " ++ printTree Type_bool
                         ++ ", actual type: " ++ printTree typ

implicitConv :: Env -> Exp -> Exp -> Err Type
implicitConv env exp1 exp2 =
   do typ1 <- inferExp env exp1
      typ2 <- inferExp env exp2
      case (typ1, typ2) of
         (Type_int, Type_int)       -> return typ1
         (Type_double, Type_double) -> return typ1
         (Type_double, Type_int)    -> return typ1
         (Type_int, Type_double)    -> return typ2
         _                          -> Bad ""

------------- Auxiliary functions -------------

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
