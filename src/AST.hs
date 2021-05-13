module AST where

import qualified Data.Set as Set
import qualified Data.Map as Map

type Var = String

data Theory = Theory (Maybe Var) (Map.Map Var Int) (Map.Map Var Equation) deriving Show

data Equation = Equation (Set.Set Var) Term Term deriving Show

data Term
  = Var Var
  | FunctionSymbol Var [Term] deriving Show

data Theorem p = Theorem p Var Equation (Proof p)

newtype Proof p = Proof [Tactic p]

data Tactic p
  = Reflexivity p
  | Symmetry p
  | Transitivity p Term
  | Congruence p [Proof p]
  | RewriteLR p Var
  | RewriteRL p Var


freeVarsOfTerm :: Term -> Set.Set Var
freeVarsOfTerm (Var x) = Set.singleton x
freeVarsOfTerm (FunctionSymbol _ args) = foldMap freeVarsOfTerm args