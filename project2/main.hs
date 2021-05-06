import System.Environment (getArgs)
import System.Exit (exitFailure)

import AbsCPP
import LexCPP
import ParCPP
import ErrM

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

-------------Auxiliary functions

--lookVar


--lookFun


--updateVar


--updateFun


--newBlock Env -> Env


--emptyEnv :: Env


