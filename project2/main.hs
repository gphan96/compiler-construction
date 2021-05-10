import System.Environment (getArgs)
import System.Exit (exitFailure)
import Data.Map (Map, insert, empty, lookup, member)

import AbsCPP
import LexCPP
import ParCPP
import ErrM

------------- Type definitions -------------

type Struct = [(Id, Type)]
type Func = ([Type], Type)
type Structs = Map Id Struct

data Entry = Var Type | Func Func

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
                                     Ok env2 -> checkStms (newBlock env2) stms
checkDef env (DStruct id field) = Bad "Struct not implemented"

checkStms :: Env -> [Stm] -> Err Env
checkStms env [] = Ok env
checkStms env (stm:xs) = case checkStm env stm of
                         Bad err -> Bad err
                         Ok env2 -> checkStms env2 xs

checkStm :: Env -> Stm -> Err Env
checkStm env (SExp exp) = case checkExp env exp of
                          Bad err -> Bad err
                          Ok env2 -> Ok env2
checkStm env (SDecls t idins) = Bad "checkStm not implemented"
checkStm env (SReturn exp) = Bad "checkStm not implemented"
checkStm env SReturnV = Bad "checkStm not implemented"
checkStm env (SWhile exp stm) = Bad "checkStm not implemented" --Task 2
checkStm env (SDoWhile stm exp) = Bad "checkStm not implemented"
checkStm env (SFor exp1 exp2 exp3 stm) = Bad "checkStm not implemented" --Task 2
checkStm env (SBlock stms) = Bad "checkStm not implemented" --Task 2
checkStm env (SIfElse exp stm1 stm2) = Bad "checkStm not implemented" --Task 2


checkExp :: Env -> Exp -> Type -> Err ()
checkExp _ _ = Bad "checkExp not implemented"


inferExp :: Env -> Exp -> Err Type

------------- Auxiliary functions -------------

extractType :: Arg -> Type
extractType (ADecl t _) = t

lookupEnv :: Env -> Id -> Err Entry
lookupEnv [] (Id id)   = Bad $ id ++ " undefined"
lookupEnv (x:xs) id  = case Data.Map.lookup id x of
                         Just entry -> Ok entry
                         Nothing    -> lookupEnv xs id

updateEnv :: Env -> Id -> Entry -> Err Env
updateEnv (x:xs) (Id id) entry = if member (Id id) x
                            then Bad $ id ++ " already declared"
                            else Ok $ [insert (Id id) entry x] ++ xs

-- Building the stack from front to back. The first element is always on top of the stack.
newBlock :: Env -> Env
newBlock env = [empty] ++ env

emptyEnv :: Env
emptyEnv = [empty]
