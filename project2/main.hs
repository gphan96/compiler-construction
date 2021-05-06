import System.Environment (getArgs)
import System.Exit (exitFailure)

import AbsCPP
import LexCPP
import ParCPP
import ErrM

------------- Type definitions -------------

type Struct = [(Id, Type)]
type Func = ([Type], Type)

data Entry = Var (Id, Type) | Func (Id, Func) | Struct (Id, Struct) | Block Env

type Env = [Entry]

------------- Main functions -------------

process :: String -> IO () 
process s = case pProgram (myLexer s) of
            Bad err  -> do putStrLn "SYNTAX ERROR"
                           putStrLn err
                           exitFailure 
            Ok  tree -> putStrLn "Type checker not implemented"

main :: IO ()
main = do args <- getArgs
          case args of
            [file] -> readFile file >>= process
            _      -> getContents >>= process

--typecheck :: Program -> Err () --main typecheck function


--checkDef :: Env -> Def -> Err ()


--checkStm


--checkExp


--infer

------------- Auxiliary functions -------------

lookVar :: Env -> Id -> Either String Type
lookVar [] (Id id)         = Left (id ++ "undefined")
lookVar (Block env:xs) id  = case lookVar env id of
                             Left _  -> lookVar xs id
                             Right t -> Right t
lookVar (Var (i, t):xs) id = if i == id 
                             then Right t 
                             else lookVar xs id
lookVar (x:xs) id          = lookVar xs id

lookFun :: Env -> Id -> Either String Func
lookFun [] (Id id)          = Left (id ++ "undefined")
lookFun (Block env:xs) id   = case lookFun env id of
                              Left _  -> lookFun xs id
                              Right f -> Right f
lookFun (Func (i, f):xs) id = if i == id 
                              then Right f 
                              else lookFun xs id
lookFun (x:xs) id           = lookFun xs id

updateVar :: Env -> Id -> Type -> Env
updateVar (Block env:xs) id t = updateVar env id t ++ xs
updateVar env id t            = [Var (id, t)] ++ env

updateFun :: Env -> Id -> Func -> Env
updateFun (Block env:xs) id f = updateFun env id f ++ xs
updateFun env id f            = [Func (id, f)] ++ env

-- Building the stack from front to back. The first element is always on top of the stack.
newBlock :: Env -> Env
newBlock env = [Block []] ++ env 

emptyEnv :: Env
emptyEnv = []
