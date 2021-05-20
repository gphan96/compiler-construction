import           System.Environment (getArgs)
import           System.Exit        (exitFailure)

import           AbsCPP
import           ErrM
import           LexCPP
import           ParCPP
import           PrintCPP

import Typechecker
import Codegenerator

process :: String -> IO ()
process s = case pProgram (myLexer s) of
            Bad err  -> do putStrLn "SYNTAX ERROR"
                           putStrLn err
                           exitFailure
            Ok  tree -> case Typechecker.typecheck tree of
                        Bad err -> do putStrLn "TYPE ERROR"
                                      putStrLn err
                                      exitFailure
                        Ok _    -> Codegenerator.generateCode tree

main :: IO ()
main = do args <- getArgs
          case args of
            [file] -> readFile file >>= process
            _      -> getContents >>= process
