{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Codegenerator where

import AbsCPP
import ErrM
import LexCPP
import ParCPP
import PrintCPP
import qualified TypedAST as TA

import Data.Word
import Data.String
import Data.List
import Data.Function
import qualified Data.Map as Map
import qualified Data.ByteString.Short as BS
import qualified Data.ByteString as B
import qualified Data.ByteString.Char8 as B.Char8

import Control.Monad.Except
import Control.Monad.State
import Control.Applicative

import LLVM.Module
import LLVM.Context
import LLVM.AST
import LLVM.AST.Global
import qualified LLVM.AST as AST
import qualified LLVM.AST.Type as T
import qualified LLVM.AST.Constant as C
import qualified LLVM.AST.Float as F
import qualified LLVM.AST.CallingConvention as CC


-------------------------------------------------------------------------------
-- Module Level
-------------------------------------------------------------------------------

newtype LLVM a = LLVM (State AST.Module a)
    deriving (Functor, Applicative, Monad, MonadState AST.Module )

runLLVM :: AST.Module -> LLVM a -> AST.Module
runLLVM mod (LLVM m) = execState m mod

emptyModule :: BS.ShortByteString -> AST.Module
emptyModule label = defaultModule { moduleName = label }

addDefn :: Definition -> LLVM ()
addDefn d = do
    defs <- gets moduleDefinitions
    modify $ \s -> s { moduleDefinitions = defs ++ [d] }

define :: AST.Type -> BS.ShortByteString -> [(AST.Type, Name)] -> [BasicBlock] -> LLVM ()
define retty label argtys body = addDefn $
    GlobalDefinition $ functionDefaults {
      name        = Name label
    , parameters  = ([Parameter ty nm [] | (ty, nm) <- argtys], False)
    , returnType  = retty
    , basicBlocks = body
    }

{--external ::  Type -> String -> [(Type, Name)] -> LLVM ()
external retty label argtys = addDefn $
    GlobalDefinition $ functionDefaults {
      name        = Name label
    , linkage     = L.External
    , parameters  = ([Parameter ty nm [] | (ty, nm) <- argtys], False)
    , returnType  = retty
    , basicBlocks = []
    }--}

-------------------------------------------------------------------------------
-- Names
-------------------------------------------------------------------------------

type Names = Map.Map BS.ShortByteString Int

uniqueName :: BS.ShortByteString -> Names -> (BS.ShortByteString, Names)
uniqueName nm ns =
    case Map.lookup nm ns of
        Nothing -> (nm,  Map.insert nm 1 ns)
        Just ix -> (BS.toShort $ B.snoc (BS.fromShort nm) (fromIntegral ix), Map.insert nm (ix+1) ns)

-------------------------------------------------------------------------------
-- Codegen State
-------------------------------------------------------------------------------

type SymbolTable = [(BS.ShortByteString, Operand)]

data CodegenState
    = CodegenState {
      currentBlock :: Name                     -- Name of the active block to append to
    , blocks       :: Map.Map Name BlockState  -- Blocks for function
    , symtab       :: [SymbolTable]            -- Function scope symbol table
    , blockCount   :: Int                      -- Count of basic blocks
    , count        :: Word                     -- Count of unnamed instructions
    , names        :: Names                    -- Name Supply
    } deriving Show

data BlockState
    = BlockState {
      idx   :: Int                            -- Block index
    , stack :: [Named Instruction]            -- Stack of instructions
    , term  :: Maybe (Named Terminator)       -- Block terminator
    } deriving Show

-------------------------------------------------------------------------------
-- Codegen Operations
-------------------------------------------------------------------------------

newtype Codegen a = Codegen { runCodegen :: State CodegenState a }
    deriving (Functor, Applicative, Monad, MonadState CodegenState )

sortBlocks :: [(Name, BlockState)] -> [(Name, BlockState)]
sortBlocks = sortBy (compare `on` (idx . snd))

createBlocks :: CodegenState -> [BasicBlock]
createBlocks m = map makeBlock $ sortBlocks $ Map.toList (blocks m)

makeBlock :: (Name, BlockState) -> BasicBlock
makeBlock (l, (BlockState _ s t)) = BasicBlock l (reverse s) (maketerm t)
    where
        maketerm (Just x) = x
        maketerm Nothing = error $ "Block has no terminator: " ++ (show l)

entryBlockName :: BS.ShortByteString
entryBlockName = "entry"

emptyBlock :: Int -> BlockState
emptyBlock i = BlockState i [] Nothing

emptyCodegen :: CodegenState
emptyCodegen = CodegenState (Name entryBlockName) Map.empty [] 1 0 Map.empty

execCodegen :: Codegen a -> CodegenState
execCodegen m = execState (runCodegen m) emptyCodegen

fresh :: Codegen Word
fresh = do
    i <- gets count
    modify $ \s -> s { count = 1 + i }
    return $ i + 1

instr :: Instruction -> AST.Type -> Codegen (Operand)
instr ins t = do
    n <- fresh
    let ref = (UnName n)
    blk <- current
    let i = stack blk
    modifyBlock (blk { stack = (ref := ins) : i } )
    return $ local t ref

instrVoid :: Instruction -> Codegen ()
instrVoid ins = do
    blk <- current
    let i = stack blk
    modifyBlock (blk { stack = (Do ins) : i } )
    return ()

terminator :: Named Terminator -> Codegen (Named Terminator)
terminator trm = do
    blk <- current
    modifyBlock (blk { term = Just trm })
    return trm

-------------------------------------------------------------------------------
-- Block Stack
-------------------------------------------------------------------------------

entry :: Codegen Name
entry = gets currentBlock

addBlock :: BS.ShortByteString -> Codegen Name
addBlock bname = do
    bls <- gets blocks
    ix  <- gets blockCount
    nms <- gets names
    let new = emptyBlock ix
        (qname, supply) = uniqueName bname nms
    modify $ \s -> s { blocks = Map.insert (Name qname) new bls
                     , blockCount = ix + 1
                     , names = supply
                     }
    return (Name qname)

setBlock :: Name -> Codegen Name
setBlock bname = do
    modify $ \s -> s { currentBlock = bname }
    return bname

getBlock :: Codegen Name
getBlock = gets currentBlock

modifyBlock :: BlockState -> Codegen ()
modifyBlock new = do
    active <- gets currentBlock
    modify $ \s -> s { blocks = Map.insert active new (blocks s) }

current :: Codegen BlockState
current = do
    c <- gets currentBlock
    blks <- gets blocks
    case Map.lookup c blks of
        Just x -> return x
        Nothing -> error $ "No such block: " ++ show c

-------------------------------------------------------------------------------
-- Symbol Table
-------------------------------------------------------------------------------

assign :: BS.ShortByteString -> Operand -> Codegen ()
assign var x = do
    tables <- gets symtab
    modify $ \s -> s { symtab = [[(var, x)] ++ head tables] ++ tail tables }

getvar :: BS.ShortByteString -> Codegen Operand
getvar var = do
    tables <- gets symtab
    getvarTable var tables

getvarTable :: BS.ShortByteString -> [SymbolTable] -> Codegen Operand
getvarTable var [] = error $ "Local variable not in scope: " ++ show var
getvarTable var (syms:xs) = case lookup var syms of
    Just x  -> return x
    Nothing -> getvarTable var xs

addTable :: Codegen ()
addTable = do
    tables <- gets symtab
    modify $ \s -> s { symtab = [[]] ++ tables }

deleteTable :: Codegen ()
deleteTable = do
    tables <- gets symtab
    modify $ \s -> s { symtab = tail tables }

-------------------------------------------------------------------------------
-- Type Mapping
-------------------------------------------------------------------------------

typeMap :: AbsCPP.Type -> AST.Type
typeMap Type_bool = IntegerType { typeBits = 1 }
typeMap Type_int = IntegerType { typeBits = 32 }
typeMap Type_double = FloatingPointType { floatingPointType = DoubleFP }
typeMap Type_void = VoidType
typeMap (TypeId id) = StructureType { isPacked = False, elementTypes = [] }

-------------------------------------------------------------------------------
-- Operators
-------------------------------------------------------------------------------

local :: AST.Type -> Name -> Operand
local typ name = LocalReference typ name

cons :: C.Constant -> Operand
cons c = ConstantOperand c

call :: Operand -> [Operand] -> AST.Type -> Codegen Operand
call fn args t = instr (Call Nothing CC.C [] (Right fn) (map (\x -> (x, [])) args) [] []) t

alloca :: AST.Type -> Codegen Operand
alloca ty = instr (Alloca ty Nothing 0 []) ty

store :: Operand -> Operand -> Codegen ()
store ptr val = instrVoid (Store False ptr val Nothing 0 [])

load :: Operand -> AST.Type -> Codegen Operand
load ptr t = instr (Load False ptr Nothing 0 []) t

ret :: Operand -> Codegen (Named Terminator)
ret val = terminator $ Do $ Ret (Just val) []

retVoid :: Codegen (Named Terminator)
retVoid = terminator $ Do $ Ret Nothing []

-------------------------------------------------------------------------------
-- Compilation
-------------------------------------------------------------------------------

strToShort :: String -> BS.ShortByteString
strToShort str = BS.toShort $ B.Char8.pack str

moduleTitle :: BS.ShortByteString
moduleTitle = "module"

codegen :: AST.Module -> TA.ProgramT -> IO AST.Module
codegen mod (TA.PDefs defs) = withContext $ \context ->
    withModuleFromAST context newast $ \m -> do
        llstr <- moduleLLVMAssembly m
        B.Char8.putStrLn llstr
        return newast
    where
        modn    = mapM codegenDef defs
        newast  = runLLVM mod modn

codegenDef :: TA.DefT -> LLVM ()
codegenDef (TA.DFun t (Id id) arg stms) = do
    define (typeMap t) (strToShort id) args bls
    where
        args = map (\(ADecl typ (Id ide)) -> (typeMap typ, Name $ strToShort ide)) arg
        bls = createBlocks $ execCodegen $ do
            entry <- addBlock entryBlockName
            setBlock entry
            addTable
            forM arg $ \(ADecl typ2 (Id id2)) -> do
                var <- alloca $ typeMap typ2
                store var $ local (typeMap typ2) (Name $ strToShort id2)
                assign (strToShort id2) var
            mapM codegenStm stms
            case last stms of
                (TA.SReturnV) -> return ()
                (TA.SReturn _) -> return ()
                _ -> do
                    retVoid
                    return ()
codegenDef (TA.DStruct id fields) = do return ()
        
codegenStm :: TA.StmT -> Codegen ()
codegenStm (TA.SExp exp) = do
    codegenExp exp
    return ()
codegenStm (TA.SDecls t idins) = codegenIdins t idins
codegenStm (TA.SReturn exp) = do
    var <- codegenExp exp
    ret var
    return ()
codegenStm TA.SReturnV = do
    retVoid
    return ()
codegenStm (TA.SWhile exp stm) = do return ()
codegenStm (TA.SDoWhile stm exp) = do return ()
codegenStm (TA.SFor exp1 exp2 exp3 stm) = do return ()
codegenStm (TA.SBlock stms) = do
    addTable
    mapM codegenStm stms
    deleteTable
codegenStm (TA.SIfElse exp stm1 stm2) = do return ()

codegenIdins :: AbsCPP.Type -> [TA.IdInT] -> Codegen ()
codegenIdins t idins = do
    forM idins $ \idin -> do
        codegenIdin t idin
    return ()

codegenIdin :: AbsCPP.Type -> TA.IdInT -> Codegen ()
codegenIdin t (TA.IdNoInit (Id id)) = do
    var <- alloca $ typeMap t
    assign (strToShort id) var
codegenIdin t (TA.IdInit (Id id) exp) = do
    res <- codegenExp exp
    var <- alloca $ typeMap t
    store var res
    assign (strToShort id) var

codegenExp :: TA.ExpT -> Codegen Operand
codegenExp (TA.ETrue, typ) = do
    return $ cons $ C.Int { C.integerBits = 1
                          , C.integerValue = 1 
                          }
codegenExp (TA.EFalse, typ) = do
    return $ cons $ C.Int { C.integerBits = 1
                          , C.integerValue = 0 
                          }
codegenExp ((TA.EInt int), typ) = do
    return $ cons $ C.Int { C.integerBits = 32
                          , C.integerValue = int 
                          }
codegenExp ((TA.EDouble double), typ) = do
    return $ cons $ C.Float { C.floatValue = (F.Double double) }
codegenExp ((TA.EId (Id id)), typ) = do
    ptr <- getvar $ strToShort id
    load ptr $ typeMap typ
codegenExp ((TA.EApp id exps), typ) = do return $ local VoidType (Name "not implemented")
codegenExp ((TA.EProj exp id), typ) = do return $ local VoidType (Name "not implemented")
codegenExp ((TA.EPIncr exp), typ) = do return $ local VoidType (Name "not implemented")
codegenExp ((TA.EPDecr exp), typ) = do return $ local VoidType (Name "not implemented")
codegenExp ((TA.EIncr exp), typ) = do return $ local VoidType (Name "not implemented")
codegenExp ((TA.EDecr exp), typ) = do return $ local VoidType (Name "not implemented")
codegenExp ((TA.EUPlus exp), typ) = do return $ local VoidType (Name "not implemented")
codegenExp ((TA.EUMinus exp), typ) = do return $ local VoidType (Name "not implemented")
codegenExp ((TA.ETimes exp1 exp2), typ) = do return $ local VoidType (Name "not implemented")
codegenExp ((TA.EDiv exp1 exp2), typ) = do return $ local VoidType (Name "not implemented")
codegenExp ((TA.EPlus exp1 exp2), typ) = do return $ local VoidType (Name "not implemented")
codegenExp ((TA.EMinus exp1 exp2), typ) = do return $ local VoidType (Name "not implemented")
codegenExp ((TA.ETwc exp1 exp2), typ) = do return $ local VoidType (Name "not implemented")
codegenExp ((TA.ELt exp1 exp2), typ) = do return $ local VoidType (Name "not implemented")
codegenExp ((TA.EGt exp1 exp2), typ) = do return $ local VoidType (Name "not implemented")
codegenExp ((TA.ELtEq exp1 exp2), typ) = do return $ local VoidType (Name "not implemented")
codegenExp ((TA.EGtEq exp1 exp2), typ) = do return  $ local VoidType (Name "not implemented")
codegenExp ((TA.EEq exp1 exp2), typ) = do return $ local VoidType (Name "not implemented")
codegenExp ((TA.ENEq exp1 exp2), typ) = do return $ local VoidType (Name "not implemented")
codegenExp ((TA.EAnd exp1 exp2), typ) = do return $ local VoidType (Name "not implemented")
codegenExp ((TA.EOr exp1 exp2), typ) = do return $ local VoidType (Name "not implemented")
codegenExp ((TA.EAss exp1 exp2), typ) = do return $ local VoidType (Name "not implemented")
codegenExp ((TA.ECond exp1 exp2 exp3), typ) = do return $ local VoidType (Name "not implemented")