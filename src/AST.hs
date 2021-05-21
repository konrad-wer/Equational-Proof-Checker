module AST where

import qualified Data.Set as Set
import qualified Data.Map as Map

type Var = String

data Session p = Session Theory [Theorem p] deriving Show

data Theory = Theory (Maybe Var) (Map.Map Var Int) (Map.Map Var Equation) deriving Show

data Equation = Equation (Set.Set Var) Term Term deriving Show

data Term
  = Var Var
  | FunctionSymbol Var [Term] deriving (Show, Eq)

data Theorem p = Theorem p Var Equation (Proof p) deriving Show

type Proof p = [Tactic p]

data Tactic p
  = Reflexivity p
  | Symmetry p
  | Transitivity p Term (Proof p) (Proof p)
  | Congruence p [Proof p]
  | RewriteLR p Var
  | RewriteRL p Var
  deriving Show

tacticPos :: Tactic p -> p
tacticPos (Reflexivity p) = p
tacticPos (Symmetry p)  = p
tacticPos (Transitivity p _ _ _) = p
tacticPos (Congruence p _) = p
tacticPos (RewriteLR p _) = p
tacticPos (RewriteRL p _) = p


freeVarsOfTerm :: Term -> Set.Set Var
freeVarsOfTerm (Var x) = Set.singleton x
freeVarsOfTerm (FunctionSymbol _ args) = foldMap freeVarsOfTerm args