import System.Environment (getArgs)
import System.Exit (exitFailure)

import qualified Data.Map as Map
import Data.Map (Map)

import AbsCPP
import LexCPP
import ParCPP
import ErrM
import PrintCPP

------------- Type definitions -------------

type Struct = [(Id, Type)]
type Func = ([Type], Type)
type Structs = Map Id Struct

data Entry = Var Type | Func Func deriving Show

type Env = [Map Id Entry]

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
typecheck (PDefs defs) = case checkDefs emptyEnv defs of
                         Bad err -> Bad err
                         Ok _    -> Ok ()
                   
checkDefs :: Env -> [Def] -> Err Env
checkDefs env [] = Ok env
checkDefs env (def:xs) = case checkDef env def of
                         Bad err -> Bad err
                         Ok env2 -> checkDefs env2 xs

checkDef :: Env -> Def -> Err Env
checkDef env (DFun t id args stms) = case updateEnv env id $ Func (map extractType args, t) of 
                                     Bad err -> Bad err
                                     Ok env2 -> case checkArgs (newBlock env2) args of
                                                Bad err -> Bad err
                                                Ok env3 -> checkStms env3 stms
checkDef env (DStruct id field) = Bad "Struct not implemented"

checkArgs :: Env -> [Arg] -> Err Env
checkArgs env []       = Ok env
checkArgs env (arg:xs) = case checkArg env arg of
                         Bad err -> Bad err
                         Ok env2 -> checkArgs env2 xs

checkArg :: Env -> Arg -> Err Env
checkArg _ (ADecl Type_void (Id id)) = Bad $ "Arguments can't be of type void, but " ++ id ++ " is"
checkArg env (ADecl t id)            = updateEnv env id $ Var t

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
checkStm env (SReturn exp) = Bad "checkStm not implemented"
checkStm env SReturnV = Bad "checkStm not implemented"
checkStm env (SWhile exp stm) = do                       --Task 2
   checkExp env exp Type_bool
   checkStm env stm
checkStm env (SDoWhile stm exp) = Bad "checkStm not implemented"
checkStm env (SFor exp1 exp2 exp3 stm) = case inferExp env exp1 of
                                         Bad err -> Bad err
                                         Ok _    -> case checkExp env exp2 Type_bool of
                                                    Bad err -> Bad err
                                                    Ok _    -> case inferExp env exp3 of
                                                               Bad err -> Bad err
                                                               Ok _    -> checkStm env stm
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
checkIdin _ (Type_void) (IdNoInit (Id id)) = Bad $ "Declarations can't be of type void, but " ++ id ++ " is"
checkIdin _ (Type_void) (IdInit (Id id) _) = Bad $ "Declarations can't be of type void, but " ++ id ++ " is"
checkIdin env t (IdNoInit id)              = updateEnv env id $ Var t
checkIdin env t (IdInit id exp)            = case checkExp env exp t of
                                             Bad err -> Bad err
                                             Ok _    -> updateEnv env id $ Var t


checkExps :: Env -> [Exp]-> [Type] -> Err ()
checkExps env [] [] = Ok ()
checkExps env (exp:xs) (t:ys) = case checkExp env exp t of
                                Bad err -> Bad err
                                Ok _    -> checkExps env xs ys

checkExp :: Env -> Exp -> Type -> Err Type
checkExp env exp t = case inferExp env exp of
                     Bad err -> Bad err
                     Ok t2   -> if t2 == t
                                then Ok t
                                else Bad $ "Expected: " ++ (show t) ++ " , but received: " ++ (show t2)


inferExp :: Env -> Exp -> Err Type
inferExp env ETrue = Ok Type_bool
inferExp env EFalse = Ok Type_bool
inferExp env (EInt int) = Ok Type_int
inferExp env (EDouble double) = Ok Type_double
inferExp env (EId (Id id)) = case lookupEnv env (Id id) of
                        Bad err -> Bad err
                        Ok (Func _) -> Bad $ id ++ " is not a variable"
                        Ok (Var t) -> Ok t
inferExp (env:xs) (EApp (Id id) exps) = case lookupEnv xs (Id id) of
                                        Bad err -> Bad err
                                        Ok (Var _) -> Bad $ id ++ " is not a function" 
                                        Ok (Func (args, ret)) -> if length args /= length exps
                                                                 then Bad $ "Expected " ++ (show $ length args) ++ " arguments, but received " ++ (show $ length exps) ++ " instead"
                                                                 else case checkExps (env:xs) exps args of
                                                                      Bad err -> Bad err
                                                                      Ok _    -> Ok ret                                                            
inferExp env (EProj exp id) = Bad "inferExp not implemented"

inferExp env (EPIncr exp) = findTypeNum env exp
inferExp env (EPDecr exp) = findTypeNum env exp
inferExp env (EIncr exp) = findTypeNum env exp
inferExp env (EDecr exp )= findTypeNum env exp
inferExp env (EUPlus exp) = findTypeNum env exp
inferExp env (EUMinus exp) = findTypeNum env exp

inferExp env (ETimes exp1 exp2) = inferArithmBin env [Type_int, Type_double] exp1 exp2
   -- case checkExps env [exp, exp2] [Type_int, Type_int] of
   --                               Ok _  -> Ok Type_int
   --                               Bad _ -> case checkExps env [exp, exp2] [Type_double, Type_double] of
   --                                        Ok _    -> Ok Type_double
   --                                        Bad err -> Bad err
inferExp env (EDiv exp1 exp2) = inferArithmBin env [Type_int, Type_double] exp1 exp2
inferExp env (EPlus exp1 exp2) = inferArithmBin env [Type_int, Type_double] exp1 exp2
inferExp env (EMinus exp1 exp2) = inferArithmBin env [Type_int, Type_double] exp1 exp2

inferExp env (ETwc exp1 exp2) = returnComparison env Type_int exp1 exp2
   -- case checkExps env [exp, exp2] [Type_int, Type_int] of
   --                             Ok _  -> Ok Type_int
   --                             Bad _ -> case checkExps env [exp, exp2] [Type_double, Type_double] of
   --                                      Ok _    -> Ok Type_int
   --                                      Bad err -> Bad err
inferExp env (ELt exp1 exp2) = returnComparison env Type_bool exp1 exp2
inferExp env (EGt exp1 exp2) = returnComparison env Type_bool exp1 exp2
inferExp env (ELtEq exp1 exp2) = returnComparison env Type_bool exp1 exp2
   -- case checkExps env [exp, exp2] [Type_int, Type_int] of
   --                              Ok _  -> Ok Type_bool
   --                              Bad _ -> case checkExps env [exp, exp2] [Type_double, Type_double] of
   --                                       Ok _    -> Ok Type_bool
   --                                       Bad err -> Bad err
inferExp env (EGtEq exp1 exp2) = returnComparison env Type_bool exp1 exp2
inferExp env (EEq exp1 exp2) = returnComparison env Type_bool exp1 exp2
inferExp env (ENEq exp1 exp2) = returnComparison env Type_bool exp1 exp2
inferExp env (EAnd exp1 exp2) = inferArithmBin env [Type_bool] exp1 exp2
inferExp env (EOr exp1 exp2) = inferArithmBin env [Type_bool] exp1 exp2

inferExp env (EAss exp1 exp2) = do typ1 <- inferExp env exp1
                                   checkExp env exp2 typ1
inferExp env (ECond exp1 exp2 exp3) = do checkExp env exp1 Type_bool
                                         inferArithmBin env [Type_int, Type_double, Type_bool] exp1 exp2


findTypeNum :: Env -> Exp -> Err Type
findTypeNum env exp = do typ <- inferExp env exp
                         if typ `elem` [Type_int, Type_double]
                         then return typ
                         else Bad $ "Type error of expression " ++ printTree exp

inferArithmBin :: Env -> [Type] -> Exp -> Exp -> Err Type
inferArithmBin env typs exp1 exp2 = do
   typ1 <- inferExp env exp1
   if typ1 `elem` typs then
      checkExp env exp2 typ1
   else Bad $ "Type error of expression " ++ printTree exp1

returnComparison :: Env -> Type -> Exp -> Exp -> Err Type
returnComparison env r_typ exp1 exp2 = do
   let typs = [Type_int, Type_double]
   case inferArithmBin env typs exp1 exp2 of
      Ok _  -> return r_typ
      Bad err -> Bad $ err

------------- Auxiliary functions -------------

extractType :: Arg -> Type
extractType (ADecl t _) = t

lookupEnv :: Env -> Id -> Err Entry
lookupEnv [] (Id id) = Bad $ id ++ " undefined"
lookupEnv (x:xs) id  = case Map.lookup id x of
                         Just entry -> Ok entry
                         Nothing    -> lookupEnv xs id

updateEnv :: Env -> Id -> Entry -> Err Env
updateEnv (x:xs) (Id id) entry = if Map.member (Id id) x
                            then Bad $ "Variable " ++ id ++ " already declared in this block"
                            else Ok $ Map.insert (Id id) entry x :xs

-- Building the stack from front to back. The first element of the list is always the top element of the stack.
newBlock :: Env -> Env
newBlock env = Map.empty:env

deleteBlock :: Env -> Env
deleteBlock (env:xs) = xs

emptyEnv :: Env
emptyEnv = [Map.empty]
