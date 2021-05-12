module AST where

import qualified Data.Set as Set
import qualified Data.Map as Map

type Var = String

type Signature = Map.Map String Integer

data Theory = Theory Signature [Equation]

data Equation = Equation (Set.Set Var) Term Term

data Term
  = Var
  | FunctionSymbol [Term]