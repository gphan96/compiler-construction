{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings          #-}

module Codegenerator where

import           AbsCPP
import           ErrM
import           LexCPP
import           ParCPP
import           PrintCPP
import qualified TypedAST                        as TA

import qualified Data.ByteString                 as B
import qualified Data.ByteString.Char8           as B.Char8
import qualified Data.ByteString.Short           as BS
import           Data.Function
import           Data.List
import qualified Data.Map                        as Map
import           Data.String
import           Data.Word

import           Control.Applicative
import           Control.Monad.Except
import           Control.Monad.State

import           LLVM.AST
import qualified LLVM.AST                        as AST
import qualified LLVM.AST.AddrSpace              as A
import qualified LLVM.AST.CallingConvention      as CC
import qualified LLVM.AST.Constant               as C
import qualified LLVM.AST.Float                  as F
import qualified LLVM.AST.FloatingPointPredicate as FP
import           LLVM.AST.Global
import qualified LLVM.AST.IntegerPredicate       as IP
import qualified LLVM.AST.Type                   as T
import           LLVM.Context
import           LLVM.Module


type Structs = [(Id, [(Id, AbsCPP.Type)])]

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

struct :: BS.ShortByteString -> [AST.Type] -> LLVM ()
struct label fields = addDefn $
    TypeDefinition (Name label) (Just StructureType {
      isPacked     = False
    , elementTypes = fields
    })

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
    , structs      :: Structs                  -- Structs
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
        maketerm Nothing  = error $ "Block has no terminator: " ++ (show l)

entryBlockName :: BS.ShortByteString
entryBlockName = "entry"

emptyBlock :: Int -> BlockState
emptyBlock i = BlockState i [] Nothing

emptyCodegen :: Structs -> CodegenState
emptyCodegen structs = CodegenState (Name entryBlockName) Map.empty [] 1 0 Map.empty structs

execCodegen :: Structs -> Codegen a -> CodegenState
execCodegen s m = execState (runCodegen m) $ emptyCodegen s

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
        Just x  -> return x
        Nothing -> error $ "No such block: " ++ show c

-------------------------------------------------------------------------------
-- Symbol Table
-------------------------------------------------------------------------------

declare :: BS.ShortByteString -> Operand -> Codegen ()
declare var x = do
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
typeMap Type_bool        = T.i1
typeMap Type_int         = T.i32
typeMap Type_double      = T.double
typeMap Type_void        = T.void
typeMap (TypeId (Id id)) = NamedTypeReference $ Name $ strToShort id

true :: Operand
true = cons $ C.Int { C.integerBits = 1
                    , C.integerValue = 1
                    }

false :: Operand
false = cons $ C.Int { C.integerBits = 1
                     , C.integerValue = 0
                     }

-------------------------------------------------------------------------------
-- Type Conversion
-------------------------------------------------------------------------------

intToDouble :: Operand -> AbsCPP.Type -> Codegen Operand
intToDouble a t = do
    case t of
        Type_int -> do
            res <- sitofp a T.double
            return res
        _ -> do
            return a

typeConv :: AbsCPP.Type -> AbsCPP.Type -> AbsCPP.Type
typeConv t1 t2 =
    if t1 == t2 then t1
    else if t1 == Type_double && t2 == Type_int || t2 == Type_double && t1 == Type_int then Type_double
    else t1 -- Shouldn't happen, if function called in the right way.

-------------------------------------------------------------------------------
-- Operators
-------------------------------------------------------------------------------

local :: AST.Type -> Name -> Operand
local typ name = LocalReference typ name

externf :: BS.ShortByteString -> AST.Type -> [AST.Type] -> Operand
externf name retty argtys = ConstantOperand $ C.GlobalReference (PointerType (FunctionType retty argtys False) (A.AddrSpace 0)) (Name name)

cons :: C.Constant -> Operand
cons c = ConstantOperand c

add :: Operand -> Operand -> Codegen Operand
add a b = instr (Add False False a b []) T.i32

fadd :: Operand -> Operand -> Codegen Operand
fadd a b = instr (FAdd noFastMathFlags a b []) T.double

sub :: Operand -> Operand -> Codegen Operand
sub a b = instr (Sub False False a b []) T.i32

fsub :: Operand -> Operand -> Codegen Operand
fsub a b = instr (FSub noFastMathFlags a b []) T.double

mul :: Operand -> Operand -> Codegen Operand
mul a b = instr (Mul False False a b []) T.i32

fmul :: Operand -> Operand -> Codegen Operand
fmul a b = instr (FMul noFastMathFlags a b []) T.double

divf :: Operand -> Operand -> Codegen Operand -- dic collides with GHC.Real
divf a b = instr (SDiv False a b []) T.i32

fdiv :: Operand -> Operand -> Codegen Operand
fdiv a b = instr (FDiv noFastMathFlags a b []) T.double

icmp :: IP.IntegerPredicate -> Operand -> Operand -> Codegen Operand
icmp cond a b = instr (ICmp cond a b []) T.i1

fcmp :: FP.FloatingPointPredicate -> Operand -> Operand -> Codegen Operand
fcmp cond a b = instr (FCmp cond a b []) T.i1

sitofp :: Operand -> AST.Type -> Codegen Operand
sitofp a typ = instr (SIToFP a typ []) typ

and :: Operand -> Operand -> Codegen Operand
and a b = instr (And a b []) T.i1

or :: Operand -> Operand -> Codegen Operand
or a b = instr (Or a b []) T.i1

call :: Operand -> [Operand] -> AST.Type -> Codegen Operand
call fn args t = instr (Call Nothing CC.C [] (Right fn) (map (\x -> (x, [])) args) [] []) t

callVoid :: Operand -> [Operand] -> Codegen ()
callVoid fn args = instrVoid (Call Nothing CC.C [] (Right fn) (map (\x -> (x, [])) args) [] [])

getelemptr :: Operand -> [Operand] -> AST.Type -> Codegen Operand
getelemptr addr idx typ = instr (GetElementPtr False addr idx []) typ

alloca :: AST.Type -> Codegen Operand
alloca ty = instr (Alloca ty Nothing 0 []) ty

store :: Operand -> Operand -> Codegen ()
store ptr val = instrVoid (Store False ptr val Nothing 0 [])

load :: Operand -> AST.Type -> Codegen Operand
load ptr t = instr (Load False ptr Nothing 0 []) t

br :: Name -> Codegen (Named Terminator)
br val = terminator $ Do $ Br val []

cbr :: Operand -> Name -> Name -> Codegen (Named Terminator)
cbr cond tr fl = terminator $ Do $ CondBr cond tr fl []

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

codegen :: AST.Module -> (TA.ProgramT, Structs) -> IO AST.Module
codegen mod ((TA.PDefs defs), structs) = withContext $ \context ->
    withModuleFromAST context newast $ \m -> do
        llstr <- moduleLLVMAssembly m
        B.Char8.putStrLn llstr
        return newast
    where
        modn    = mapM (codegenDef structs) defs
        newast  = runLLVM mod modn


codegenDef :: Structs -> TA.DefT -> LLVM ()
codegenDef structs (TA.DFun t (Id id) arg stms) = do
    define (typeMap t) (strToShort id) args bls
    where
        args = map (\(ADecl typ (Id ide)) -> (typeMap typ, Name $ strToShort ide)) arg
        bls = createBlocks $ execCodegen structs $ do
            entry <- addBlock entryBlockName
            setBlock entry
            addTable
            forM arg $ \(ADecl typ2 (Id id2)) -> do
                var <- alloca $ typeMap typ2
                store var $ local (typeMap typ2) (Name $ strToShort id2)
                declare (strToShort id2) var
            --mapM (codegenStm t) stms
            codegenStms t stms
            if stms == [] then do
                retVoid
                return ()
            else case last stms of
                (TA.SReturnV) -> return ()
                (TA.SReturn _) -> return ()
                _ -> do
                    case t of
                        Type_void -> do
                            retVoid
                            return ()
                        _ -> do
                            cur <- current
                            case cur of
                                (BlockState _ _ Nothing) -> do
                                    defPtr <- alloca $ typeMap t
                                    defRet <- load defPtr $ typeMap t
                                    ret defRet
                                    return ()
                                _ -> do return ()

codegenDef _ (TA.DStruct (Id id) fields) = do
    struct (strToShort id) fs
    where
        fs = map (\(FDecl t _) -> typeMap t) fields

containsReturn :: TA.StmT -> Bool
containsReturn (TA.SBlock stms) = any (\x -> case x of
  (TA.SBlock stms2) -> containsReturn (TA.SBlock stms2)
  TA.SReturnV  -> True
  TA.SReturn _ -> True
  _            -> False) stms
containsReturn (TA.SReturnV) = True
containsReturn (TA.SReturn e) = True
containsReturn _ = False

codegenStms :: AbsCPP.Type -> [TA.StmT] -> Codegen ()
codegenStms t []       = return ()
codegenStms t (stm:xs) = case stm of
    ((TA.SReturn e)) -> do
        codegenStm t (TA.SReturn e)
        return ()
    (TA.SReturnV)    -> do
        codegenStm t (TA.SReturnV)
        return ()
    (TA.SDoWhile st _) -> checkReturn st
    (TA.SWhile _ st)   -> checkReturn st
    (TA.SBlock stms)   -> checkReturn (TA.SBlock stms)
    (TA.SFor _ _ _ st) -> do
        codegenStm t stm
        codegenStms t xs
    _                  -> do
        codegenStm t stm
        codegenStms t xs
    where
        checkReturn st =
            if containsReturn st then do
                codegenStm t stm
                return ()
            else do
                codegenStm t stm
                codegenStms t xs

codegenStm :: AbsCPP.Type -> TA.StmT -> Codegen ()
codegenStm _ (TA.SExp exp) = do
    codegenExp exp
    return ()
codegenStm _ (TA.SDecls t idins) = codegenIdins t idins
codegenStm retty (TA.SReturn (exp, t)) = do
    var <- codegenExp (exp, t)
    if retty == Type_double && t == Type_int then do
        conv <- sitofp var $ typeMap retty
        ret conv
        return ()
    else do
        ret var
        return ()
codegenStm _ TA.SReturnV = do
    retVoid
    return ()
codegenStm ret (TA.SWhile exp stm) = do
    whileCond <- addBlock "while.cond"
    whileBlock <- addBlock "while.block"
    br whileCond
    setBlock whileCond
    cond <- codegenExp exp
    if containsReturn stm then do
        br whileBlock
        setBlock whileBlock
        codegenStm ret stm
    else do
        continue <- addBlock "continue"
        cbr cond whileBlock continue
        setBlock whileBlock
        codegenStm ret stm
        br whileCond
        setBlock continue
        return ()
codegenStm retty (TA.SDoWhile stm exp) = do
    whileBlock <- addBlock $ strToShort "whileBlock"
    br whileBlock
    if containsReturn stm then do
        setBlock whileBlock
        codegenStm retty stm
    else do
        whileCond <- addBlock $ strToShort "whileCond"
        continue  <- addBlock $ strToShort "continue"
        setBlock whileCond
        cond <- codegenExp exp
        cbr cond whileBlock continue
        setBlock whileBlock
        codegenStm retty stm
        br whileCond
        setBlock continue
        return ()
codegenStm retty (TA.SFor exp1 exp2 exp3 stm) = do
    forCond <- addBlock $ strToShort "forCond"
    forLoop <- addBlock $ strToShort "forLoop"
    continue <- addBlock $ strToShort "continue"
    codegenExp exp1
    br forCond
    setBlock forCond
    con <- codegenExp exp2
    cbr con forLoop continue
    setBlock forLoop
    codegenStm retty stm
    if containsReturn stm then do
        setBlock continue
        return ()
    else do
        codegenExp exp3
        br forCond
        setBlock continue
        return ()
codegenStm retty (TA.SBlock stms) = do
    addTable
    --mapM (codegenStm retty) stms
    codegenStms retty stms
    deleteTable
codegenStm retty (TA.SIfElse exp stm1 stm2) = do -- TODO: clean this up
    ifThen <- addBlock $ strToShort "ifThen"
    ifElse <- addBlock $ strToShort "ifElse"
--
    con <- codegenExp exp
    cbr con ifThen ifElse
--
    if containsReturn stm1 then do
        setBlock ifThen
        codegenStm retty stm1
        if containsReturn stm2 then do
            setBlock ifElse
            codegenStm retty stm2
            return ()
        else do
            continue <- addBlock $ strToShort "continue"
            setBlock ifElse
            codegenStm retty stm2
            br continue
            setBlock continue
            return ()
    else do
        continue <- addBlock $ strToShort "continue"
        setBlock ifThen
        codegenStm retty stm1
        br continue
        setBlock continue
        if containsReturn stm2 then do
            setBlock ifElse
            codegenStm retty stm2
            return ()
        else do
            setBlock ifElse
            codegenStm retty stm2
            br continue
            setBlock continue
            return ()
--
codegenIdins :: AbsCPP.Type -> [TA.IdInT] -> Codegen ()
codegenIdins t idins = do
    forM idins $ \idin -> do
        codegenIdin t idin
    return ()

codegenIdin :: AbsCPP.Type -> TA.IdInT -> Codegen ()
codegenIdin t (TA.IdNoInit (Id id)) = do
    var <- alloca $ typeMap t
    declare (strToShort id) var
codegenIdin t (TA.IdInit (Id id) (exp, expType)) = do
    res <- codegenExp (exp, expType)
    var <- alloca $ typeMap t
    if t == Type_double && expType == Type_int then do
        conv <- sitofp res $ typeMap t
        store var conv
        declare (strToShort id) var
    else do
        store var res
        declare (strToShort id) var

codegenExp :: TA.ExpT -> Codegen Operand
codegenExp (TA.ETrue, typ) = do
    return true
codegenExp (TA.EFalse, typ) = do
    return false
codegenExp ((TA.EInt int), typ) = do
    return $ cons $ C.Int { C.integerBits = 32
                          , C.integerValue = int
                          }
codegenExp ((TA.EDouble double), typ) = do
    return $ cons $ C.Float { C.floatValue = (F.Double double) }
codegenExp ((TA.EId (Id id)), typ) = do
    ptr <- getvar $ strToShort id
    load ptr $ typeMap typ
codegenExp ((TA.EApp (Id id) exps), Type_void) = do
    args <- mapM codegenExp exps
    callVoid (externf (strToShort id) T.void argtys) args
    return $ ConstantOperand $ C.Null T.void
    where
        argtys = map (\(e, t) -> typeMap t) exps
codegenExp ((TA.EApp (Id id) exps), typ) = do
    args <- mapM codegenExp exps
    call (externf (strToShort id) (typeMap typ) argtys) args $ typeMap typ
    where
        argtys = map (\(e, t) -> typeMap t) exps
codegenExp ((TA.EProj (e, (TypeId tid)) id), typ) = do
    strs <- gets structs
    case lookup tid strs of
        Nothing -> do return $ local VoidType (Name "IMPOSSIBLE")
        Just str -> case findIndex (\(tid2, typ2) -> tid2 == id) str of
            Nothing -> do return $ local VoidType (Name "IMPOSSIBLE")
            Just index -> do
                struct <- codegenExp (e, (TypeId tid))
                ptr <- alloca $ typeMap (TypeId tid)
                store ptr struct
                elemPtr <- getelemptr ptr [cons $ C.Int 32 0, cons $ C.Int 32 $ toInteger index] $ typeMap typ
                elem <- load elemPtr $ typeMap typ
                return elem
codegenExp ((TA.EPIncr exp), typ) = case exp of
    (TA.EId _, _) -> do
        ptr <- getProjPointer exp
        val <- load ptr $ typeMap typ
        case typ of
            Type_int -> do
                res <- add val $ cons $ C.Int 32 1
                store ptr res
                return val
            Type_double -> do
                res <- fadd val $ cons $ C.Float $ F.Double 1.0
                store ptr res
                return val
            _ -> do return $ local VoidType (Name "IMPOSSIBLE")
    (TA.EProj _ _, _) -> do
        ptr <- getProjPointer exp
        val <- load ptr $ typeMap typ
        case typ of
            Type_int -> do
                res <- add val $ cons $ C.Int 32 1
                store ptr res
                return val
            Type_double -> do
                res <- fadd val $ cons $ C.Float $ F.Double 1.0
                store ptr res
                return val
            _ -> do return $ local VoidType (Name "IMPOSSIBLE")
    exp2 -> do
        res <- codegenExp exp
        return res
codegenExp ((TA.EPDecr exp), typ) = case exp of
    (TA.EId _, _) -> do
        ptr <- getProjPointer exp
        val <- load ptr $ typeMap typ
        case typ of
            Type_int -> do
                res <- sub val $ cons $ C.Int 32 1
                store ptr res
                return val
            Type_double -> do
                res <- fsub val $ cons $ C.Float $ F.Double 1.0
                store ptr res
                return val
            _ -> do return $ local VoidType (Name "IMPOSSIBLE")
    (TA.EProj _ _, _) -> do
        ptr <- getProjPointer exp
        val <- load ptr $ typeMap typ
        case typ of
            Type_int -> do
                res <- sub val $ cons $ C.Int 32 1
                store ptr res
                return val
            Type_double -> do
                res <- fsub val $ cons $ C.Float $ F.Double 1.0
                store ptr res
                return val
            _ -> do return $ local VoidType (Name "IMPOSSIBLE")
    exp2 -> do
        res <- codegenExp exp
        return res
codegenExp ((TA.EIncr exp), typ) = case exp of
    (TA.EId _, _) -> do
        ptr <- getProjPointer exp
        val <- load ptr $ typeMap typ
        case typ of
            Type_int -> do
                res <- add val $ cons $ C.Int 32 1
                store ptr res
                return res
            Type_double -> do
                res <- fadd val $ cons $ C.Float $ F.Double 1.0
                store ptr res
                return res
            _ -> do return $ local VoidType (Name "IMPOSSIBLE")
    (TA.EProj _ _, _) -> do
        ptr <- getProjPointer exp
        val <- load ptr $ typeMap typ
        case typ of
            Type_int -> do
                res <- add val $ cons $ C.Int 32 1
                store ptr res
                return res
            Type_double -> do
                res <- fadd val $ cons $ C.Float $ F.Double 1.0
                store ptr res
                return res
            _ -> do return $ local VoidType (Name "IMPOSSIBLE")
    exp2 -> do
        res <- codegenExp exp
        return res
codegenExp ((TA.EDecr exp), typ) = case exp of
    (TA.EId _, _) -> do
        ptr <- getProjPointer exp
        val <- load ptr $ typeMap typ
        case typ of
            Type_int -> do
                res <- sub val $ cons $ C.Int 32 1
                store ptr res
                return res
            Type_double -> do
                res <- fsub val $ cons $ C.Float $ F.Double 1.0
                store ptr res
                return res
            _ -> do return $ local VoidType (Name "IMPOSSIBLE")
    (TA.EProj _ _, _) -> do
        ptr <- getProjPointer exp
        val <- load ptr $ typeMap typ
        case typ of
            Type_int -> do
                res <- sub val $ cons $ C.Int 32 1
                store ptr res
                return res
            Type_double -> do
                res <- fsub val $ cons $ C.Float $ F.Double 1.0
                store ptr res
                return res
            _ -> do return $ local VoidType (Name "IMPOSSIBLE")
    exp2 -> do
        res <- codegenExp exp
        return res
codegenExp ((TA.EUPlus exp), typ) = codegenExp exp
codegenExp ((TA.EUMinus exp), typ) = do
    var <- codegenExp exp
    case typ of
        Type_int -> do
            res <- mul var $ cons $ C.Int 32 (-1)
            return res
        Type_double -> do
            res <- fmul var $ cons $ C.Float $ F.Double (-1.0)
            return res
codegenExp ((TA.ETimes (exp1, t1) (exp2, t2)), typ) = case typ of
    Type_int -> do
        var1 <- codegenExp (exp1, t1)
        var2 <- codegenExp (exp2, t2)
        res <- mul var1 var2
        return res
    Type_double -> do
        var1 <- codegenExp (exp1, t1)
        var2 <- codegenExp (exp2, t2)
        var3 <- intToDouble var1 t1
        var4 <- intToDouble var2 t2
        res <- fmul var3 var4
        return res
    _ -> do return $ local VoidType (Name "IMPOSSIBLE")
codegenExp ((TA.EDiv (exp1, t1) (exp2, t2)), typ) = case typ of
    Type_int -> do
        var1 <- codegenExp (exp1, t1)
        var2 <- codegenExp (exp2, t2)
        res <- Codegenerator.divf var1 var2
        res <- divf var1 var2
        return res
    Type_double -> do
        var1 <- codegenExp (exp1, t1)
        var2 <- codegenExp (exp2, t2)
        var3 <- intToDouble var1 t1
        var4 <- intToDouble var2 t2
        res <- fcmp FP.OLE var3 var4
        res <- fdiv var3 var4
        return res
    _ -> do return $ local VoidType (Name "IMPOSSIBLE")
codegenExp ((TA.EPlus (e1, t1) (e2, t2)), typ) = do
    var1 <- codegenExp (e1, t1)
    var2 <- codegenExp (e2, t2)
    case typ of
        Type_int -> do
            res <- add var1 var2
            return res
        Type_double -> do
            var3 <- intToDouble var1 t1
            var4 <- intToDouble var2 t2
            res <- fadd var3 var4
            return res
        _ -> do return $ local VoidType (Name "IMPOSSIBLE")
codegenExp ((TA.EMinus (exp1, t1) (exp2, t2)), typ) = do
    var1 <- codegenExp (exp1, t1)
    var2 <- codegenExp (exp2, t2)
    case typ of
        Type_int -> do
            sub var1 var2
        Type_double -> do
            var1' <- intToDouble var1 t1
            var2' <- intToDouble var2 t2
            fsub var1' var2'
        _ -> do return $ local VoidType (Name "IMPOSSIBLE")
codegenExp ((TA.ETwc (e1, t1) (e2, t2)), typ) = do
    lt <- addBlock $ strToShort "lt"
    ge <- addBlock $ strToShort "ge"
    gt <- addBlock $ strToShort "gt"
    continue <- addBlock "continue"
    var1 <- codegenExp (e1, t1)
    var2 <- codegenExp (e2, t2)
    ptr <- alloca T.i32
    store ptr $ cons $ C.Int 32 0
    if typeConv t1 t2 == Type_double then do
        var3 <- intToDouble var1 t1
        var4 <- intToDouble var2 t2
        less <- fcmp FP.OLT var3 var4
        cbr less lt ge
        setBlock ge
        greater <- fcmp FP.OGT var3 var4
        cbr greater gt continue
    else do
        less <- icmp IP.SLT var1 var2
        cbr less lt ge
        setBlock ge
        greater <- icmp IP.SGT var1 var2
        cbr greater gt continue
    setBlock lt
    store ptr $ cons $ C.Int 32 (-1)
    br continue
    setBlock gt
    store ptr $ cons $ C.Int 32 (1)
    br continue
    setBlock continue
    res <- load ptr T.i32
    return res
codegenExp ((TA.ELt (e1, t1) (e2, t2)), typ) = case typeConv t1 t2 of
    Type_int -> do
        var1 <- codegenExp (e1, t1)
        var2 <- codegenExp (e2, t2)
        res <- icmp IP.SLT var1 var2
        return res
    Type_double -> do
        var1 <- codegenExp (e1, t1)
        var2 <- codegenExp (e2, t2)
        var3 <- intToDouble var1 t1
        var4 <- intToDouble var2 t2
        res <- fcmp FP.OLT var3 var4
        return res
    _ -> do return $ local VoidType (Name "IMPOSSIBLE")
codegenExp ((TA.EGt (exp1, t1) (exp2, t2)), typ) = do
    var1 <- codegenExp (exp1, t1)
    var2 <- codegenExp (exp2, t2)
    case typeConv t1 t2 of
        Type_int -> do
            icmp IP.SGT var1 var2
        Type_double -> do
            var1' <- intToDouble var1 t1
            var2' <- intToDouble var2 t2
            fcmp FP.OGT var1' var2'
        _ -> do return $ local VoidType (Name "IMPOSSIBLE")
codegenExp ((TA.ELtEq (e1, t1) (e2, t2)), typ) = case typeConv t1 t2 of
    Type_int -> do
        var1 <- codegenExp (e1, t1)
        var2 <- codegenExp (e2, t2)
        res <- icmp IP.SLE var1 var2
        return res
    Type_double -> do
        var1 <- codegenExp (e1, t1)
        var2 <- codegenExp (e2, t2)
        var3 <- intToDouble var1 t1
        var4 <- intToDouble var2 t2
        res <- fcmp FP.OLE var3 var4
        return res
    _ -> do return $ local VoidType (Name "IMPOSSIBLE")
codegenExp ((TA.EGtEq (e1, t1) (e2, t2)), typ) = case typeConv t1 t2 of
    Type_int -> do
        var1 <- codegenExp (e1, t1)
        var2 <- codegenExp (e2, t2)
        res <- icmp IP.SGE var1 var2
        return res
    Type_double -> do
        var1 <- codegenExp (e1, t1)
        var2 <- codegenExp (e2, t2)
        var3 <- intToDouble var1 t1
        var4 <- intToDouble var2 t2
        res <- fcmp FP.OGE var3 var4
        return res
    _ -> do return $ local VoidType (Name "IMPOSSIBLE") 
codegenExp ((TA.EEq (exp1, t1) (exp2, t2)), typ) = do
    val1 <- codegenExp (exp1, t1)
    val2 <- codegenExp (exp2, t2)
    equal (val1, (exp1, t1), t1) (val2, (exp2, t2), t2)
codegenExp ((TA.ENEq (exp1, t1) (exp2, t2)), typ) = do
    val1 <- codegenExp (exp1, t1)
    val2 <- codegenExp (exp2, t2)
    notEqual (val1, (exp1, t1), t1) (val2, (exp2, t2), t2)
codegenExp ((TA.EAnd exp1 exp2), typ) = do
    var1 <- codegenExp exp1
    var2 <- codegenExp exp2
    res <- Codegenerator.and var1 var2
    return res
codegenExp ((TA.EOr exp1 exp2), typ) = do
    var1 <- codegenExp exp1
    var2 <- codegenExp exp2
    res <- Codegenerator.or var1 var2
    return res
codegenExp ((TA.EAss (exp1, t1) (exp2, t2)), typ) = do
    res <- codegenExp (exp2, t2)
    ptr <- getProjPointer (exp1, t1)
    if t2 == Type_int && t1 == Type_double then do
        conv <- sitofp res $ typeMap t1
        store ptr conv
        return conv
    else do
        store ptr res
        return res
codegenExp ((TA.ECond exp1 (exp2, t2) (exp3, t3)), typ) = do
    left <- addBlock $ strToShort "ternOpLeft"
    right <- addBlock $ strToShort "ternOpRight"
    continue <- addBlock $ strToShort "continue"
    ptr <- alloca $ typeMap typ
    cond <- codegenExp exp1
    cbr cond left right
    setBlock left
    resL <- codegenExp (exp2, t2)
    if typ == Type_double && t2 == Type_int then do
        convL <- sitofp resL $ typeMap typ
        store ptr convL
    else do
        store ptr resL
    br continue
    setBlock right
    resR <- codegenExp (exp3, t3)
    if typ == Type_double && t3 == Type_int then do
        convR <- sitofp resR $ typeMap typ
        store ptr convR
    else do
        store ptr resR
    br continue
    setBlock continue
    res <- load ptr $ typeMap typ
    return res

equal :: (Operand, TA.ExpT, AbsCPP.Type) -> (Operand, TA.ExpT, AbsCPP.Type) -> Codegen Operand
equal (a, e1, t1) (b, e2, t2) = do
    if t1 == Type_double && t2 == Type_int || t2 == Type_double && t1 == Type_int then do
        var1 <- intToDouble a t1
        var2 <- intToDouble b t2
        res <- fcmp FP.OEQ var1 var2
        return res
    else if t1 == t2 then do
        case t1 of
            Type_int -> do
                res <- icmp IP.EQ a b
                return res
            Type_double -> do
                res <- fcmp FP.OEQ a b
                return res
            Type_bool -> do
                res <- icmp IP.EQ a b
                return res
            Type_void -> do
                return true
            (TypeId id) -> do
                ptr <- alloca T.i1
                store ptr true
                strs <- gets structs
                case lookup id strs of
                    Nothing -> do return $ local VoidType (Name "IMPOSSIBLE")
                    Just fields -> do
                        mapM (\(idf, typ) -> do
                            c1 <- codegenExp ((TA.EProj e1 idf), typ)
                            c2 <- codegenExp ((TA.EProj e2 idf), typ)
                            comp <- equal (c1, ((TA.EProj e1 idf), typ), typ) (c2, ((TA.EProj e2 idf), typ), typ)
                            old <- load ptr T.i1
                            new <- Codegenerator.and old comp
                            store ptr new
                            ) fields
                        result <- load ptr T.i1
                        return result
    else do
        return false

notEqual :: (Operand, TA.ExpT, AbsCPP.Type) -> (Operand, TA.ExpT, AbsCPP.Type) -> Codegen Operand
notEqual (a, e1, t1) (b, e2, t2) = do
    if t1 == Type_double && t2 == Type_int || t2 == Type_double && t1 == Type_int then do
        var1 <- intToDouble a t1
        var2 <- intToDouble b t2
        res <- fcmp FP.ONE var1 var2
        return res
    else if t1 == t2 then do
        case t1 of
            Type_int -> do
                res <- icmp IP.NE a b
                return res
            Type_double -> do
                res <- fcmp FP.ONE a b
                return res
            Type_bool -> do
                res <- icmp IP.NE a b
                return res
            Type_void -> do
                return true
            (TypeId id) -> do
                ptr <- alloca T.i1
                store ptr false
                strs <- gets structs
                case lookup id strs of
                    Nothing -> do return $ local VoidType (Name "IMPOSSIBLE")
                    Just fields -> do
                        mapM (\(idf, typ) -> do
                            c1 <- codegenExp ((TA.EProj e1 idf), typ)
                            c2 <- codegenExp ((TA.EProj e2 idf), typ)
                            comp <- equal (c1, ((TA.EProj e1 idf), typ), typ) (c2, ((TA.EProj e2 idf), typ), typ)
                            old <- load ptr T.i1
                            new <- Codegenerator.or old comp
                            store ptr new
                            ) fields
                        result <- load ptr T.i1
                        return result
    else do
        return true

getProjPointer :: TA.ExpT -> Codegen Operand
getProjPointer (TA.EId (Id id), t) = do
    ptr <- getvar (strToShort id)
    return ptr
getProjPointer ((TA.EProj (exp, (TypeId tid)) id), typ) = do
    strs <- gets structs
    case lookup tid strs of
        Nothing -> do return $ local VoidType (Name "IMPOSSIBLE")
        Just str -> case findIndex (\(tid2, typ2) -> tid2 == id) str of
            Nothing -> do return $ local VoidType (Name "IMPOSSIBLE")
            Just index -> do
                ptr <- getProjPointer (exp, (TypeId tid))
                elemPtr <- getelemptr ptr [cons $ C.Int 32 0, cons $ C.Int 32 $ toInteger index] $ typeMap typ
                return elemPtr
getProjPointer _ = do return $ local VoidType (Name "IMPOSSIBLE")
