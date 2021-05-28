{-# LANGUAGE GeneralizedNewtypeDeriving #-}

-- | The types for the annotated AST returned from the typechecker.

module TypedAST where

import Prelude (Double, Integer, String)
import qualified Prelude as C (Eq, Ord, Show, Read)
import qualified Data.String

import AbsCPP

data ProgramT = PDefs [DefT]
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data DefT = DFun Type Id [Arg] [StmT] | DStruct Id [Field]
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data StmT
    = SExp ExpT
    | SDecls Type [IdInT]
    | SReturn ExpT
    | SReturnV
    | SWhile ExpT StmT
    | SDoWhile StmT ExpT
    | SFor ExpT ExpT ExpT StmT
    | SBlock [StmT]
    | SIfElse ExpT StmT StmT
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data IdInT = IdNoInit Id | IdInit Id ExpT
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data E
    = ETrue
    | EFalse
    | EInt Integer
    | EDouble Double
    | EId Id
    | EApp Id [ExpT]
    | EProj ExpT Id
    | EPIncr ExpT
    | EPDecr ExpT
    | EIncr ExpT
    | EDecr ExpT
    | EUPlus ExpT
    | EUMinus ExpT
    | ETimes ExpT ExpT
    | EDiv ExpT ExpT
    | EPlus ExpT ExpT
    | EMinus ExpT ExpT
    | ETwc ExpT ExpT
    | ELt ExpT ExpT
    | EGt ExpT ExpT
    | ELtEq ExpT ExpT
    | EGtEq ExpT ExpT
    | EEq ExpT ExpT
    | ENEq ExpT ExpT
    | EAnd ExpT ExpT
    | EOr ExpT ExpT
    | EAss ExpT ExpT
    | ECond ExpT ExpT ExpT
  deriving (C.Eq, C.Ord, C.Show, C.Read)

type ExpT = (E, Type)
