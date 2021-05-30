{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}

module AST where

import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.List (intercalate)

type Var = String

data Session p = Session Theory [Theorem p] deriving Show

data Theory = Theory (Maybe Var) (Map.Map Var Int) (Map.Map Var Equation) deriving Show

data Equation = Equation (Set.Set Var) (Term Closed) (Term Closed) deriving Show

data TermKind = Open | Closed
data Term :: TermKind -> * where
  Var :: Var -> Term k
  UnificationVar :: Var -> Term Open
  FunctionSymbol :: Var -> [Term k] -> Term k

addParens :: String -> String
addParens = ("(" ++) . (++ ")")

instance Show (Term k) where
  show (Var x) = x
  show (UnificationVar x) = "~" ++ x
  show (FunctionSymbol f []) = f
  show (FunctionSymbol f args) = f ++ addParens (intercalate "," $ show <$> args)

instance Eq (Term k) where
  Var x == Var y = x == y
  UnificationVar x == UnificationVar y = x == y
  FunctionSymbol f args == FunctionSymbol f' args' = f == f' && and (zipWith (==) args args')
  _ == _ = False

data Theorem p = Theorem p Var Equation (Proof p) deriving Show

type Proof p = [Tactic p]

data Side = LeftSide | RightSide | BothSides

data Tactic p
  = Reflexivity p
  | Symmetry p
  | Transitivity p (Term Closed) (Proof p) (Proof p)
  | Congruence p [Proof p]
  | RewriteLR p Side Var (Map.Map Var (Term Closed))
  | RewriteRL p Side Var (Map.Map Var (Term Closed))
  | Apply p Var

instance Show Side where
  show LeftSide = " left"
  show RightSide = " right"
  show BothSides = ""

instance Show (Tactic p) where
  show (Reflexivity _) = "reflexivity"
  show (Symmetry _) = "symmetry"
  show (Transitivity _ t _ _) = "transitivity " ++ show t
  show (Congruence _ _) = "congruence"
  show (Apply _ equation) = "apply "  ++ equation
  show (RewriteLR _ side equation bindings) = "rewrite" ++ show side ++ " -> " ++ equation
     ++ (if Map.null bindings then "" else " with " ++ showBindings bindings)
  show (RewriteRL _ side equation bindings) = "rewrite" ++ show side ++ " <- " ++ equation
    ++ (if Map.null bindings then "" else " with " ++ showBindings bindings)

showBindings :: Map.Map Var (Term k) -> String
showBindings bindings =
  let (l, r) = unzip $ Map.toList bindings in
  intercalate ", " (zipWith (\l r -> l ++ " := " ++ show r) l r)

tacticPos :: Tactic p -> p
tacticPos (Reflexivity p) = p
tacticPos (Symmetry p)  = p
tacticPos (Transitivity p _ _ _) = p
tacticPos (Apply p _) = p
tacticPos (Congruence p _) = p
tacticPos (RewriteLR p _ _ _) = p
tacticPos (RewriteRL p _ _ _) = p

freeVarsOfTerm :: Term Closed -> Set.Set Var
freeVarsOfTerm (Var x) = Set.singleton x
freeVarsOfTerm (FunctionSymbol _ args) = foldMap freeVarsOfTerm args