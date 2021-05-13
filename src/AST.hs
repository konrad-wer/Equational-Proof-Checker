module AST where

import qualified Data.Set as Set
import qualified Data.Map as Map

type Var = String

type Signature = Map.Map String Int

data Theory = Theory (Maybe Var) Signature [Equation] deriving Show

data Equation = Equation (Set.Set Var) Term Term deriving Show

data Term
  = Var Var
  | FunctionSymbol Var [Term] deriving Show

freeVarsOfTerm :: Term -> Set.Set Var
freeVarsOfTerm (Var x) = Set.singleton x
freeVarsOfTerm (FunctionSymbol _ args) = foldMap freeVarsOfTerm args