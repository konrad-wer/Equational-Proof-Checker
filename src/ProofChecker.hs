{-# LANGUAGE GADTs #-}


module ProofChecker where

import AST
import Control.Monad.State
import qualified Data.Map as Map
import qualified Data.Set as Set
import Text.Megaparsec.Pos

data ProofStatus p
  = Finished
  | InProgress (Set.Set Var) Term Term
  | NewGoals (Set.Set Var) [(Term, Term)] [Proof p]

data ProofError p
  = ReflexivityError p Term Term
  | UndefinedVariableInTremError p Var
  | UnfinishedProof Term Term
  | UnusedTactics p
  | CongruenceError p Term Term
  | WrongNumberOfSubproofsError p Int Int

instance SourcePos ~ p => Show (ProofError p) where
  show (ReflexivityError p t1 t2) = sourcePosPretty p ++ "\nReflexivity failure: terms are not equal " ++
    show t1 ++ ", " ++ show t2
  show (UndefinedVariableInTremError p x) = sourcePosPretty p ++ "\nVariable not in scope: " ++ x
  show (UnfinishedProof t1 t2) = "Unfinished proof: " ++ show t1 ++ " = " ++ show t2
  show (UnusedTactics p) = sourcePosPretty p ++ "\nUnused tactics left"
  show (CongruenceError p t1 t2) = sourcePosPretty p ++ "\nCould not apply congruence to terms: " ++
    show t1 ++ ", " ++ show t2
  show (WrongNumberOfSubproofsError p expected actual) = sourcePosPretty p ++
    "\nWrong number of subproofs. Expected " ++ show expected ++ ", but found: " ++ show actual


type ProofState p = StateT Int (Either (ProofError p))

reflexivity :: p -> Term -> Term -> ProofState p (ProofStatus p)
reflexivity pos t1 t2
  | t1 == t2 = return Finished
  | otherwise = lift . Left $ ReflexivityError pos t1 t2

congruence :: p ->  Equation -> [Proof p] -> ProofState p (ProofStatus p)
congruence pos (Equation vars t1@(FunctionSymbol f args) t2@(FunctionSymbol g args')) subproofs
  | f == g && length args == length args' =
    if length args == length subproofs then
      return $ NewGoals vars (zip args args') subproofs
    else
      lift . Left $ WrongNumberOfSubproofsError pos (length args) (length subproofs)
  | otherwise = lift . Left $ CongruenceError pos t1 t2
congruence pos (Equation _ t1 t2) _ = lift . Left $ CongruenceError pos t1 t2

isTermWellFounded :: p -> Set.Set Var -> Term -> ProofState p ()
isTermWellFounded pos vars (Var x)
  | x `Set.member` vars = return ()
  | otherwise = lift . Left $ UndefinedVariableInTremError pos x
isTermWellFounded pos vars (FunctionSymbol _ args) =
  mapM_ (isTermWellFounded pos vars) args

proofStep :: Theory  -> Equation -> Tactic p -> ProofState p (ProofStatus p)
proofStep _ (Equation _ t1 t2) (Reflexivity pos) = reflexivity pos t1 t2
proofStep _ (Equation vars t1 t2) (Symmetry _) = return $ InProgress vars t2 t1
proofStep _ equation (Congruence pos subproofs) = congruence pos equation subproofs
proofStep _ (Equation vars t1 t2) (Transitivity pos t proof1 proof2) = do
  isTermWellFounded pos vars t
  return $ NewGoals vars [(t1, t), (t, t2)] [proof1, proof2]
proofStep _ _ _ = undefined

check :: Theory -> Equation -> Proof p -> Either (ProofError p) ()
check theory (Equation vs term1 term2) proof =
  flip evalStateT 0 $ chk theory vs (Just (term1, term2)) proof [] []
  where
    chk ::
      Theory -> Set.Set Var ->
      Maybe (Term, Term) -> Proof p ->
      [(Term, Term)] -> [Proof p] -> ProofState p ()
    chk equations vars Nothing [] [] [] = return ()
    chk equations vars Nothing [] (goal : unfocusedGoals) (proof : unfocusedProofs) =
      chk equations vars (Just goal) proof unfocusedGoals unfocusedProofs
    chk equations vars Nothing (tactic : _) _ _ = lift . Left . UnusedTactics $ tacticPos tactic
    chk equations vars (Just (t1, t2)) [] unfocusedGoals unfocusedProofs =
      lift . Left $ UnfinishedProof t1 t2
    chk equations vars (Just (t1, t2)) (tactic : proof) unfocusedGoals unfocusedProofs = do
      stepRes <- proofStep theory (Equation vars t1 t2) tactic
      case stepRes of
        Finished -> chk equations vars Nothing proof unfocusedGoals unfocusedProofs
        InProgress vars' t1 t2 -> chk equations vars' (Just (t1, t2)) proof unfocusedGoals unfocusedProofs
        NewGoals vars' goals proofs ->
          case proof of
            [] -> chk equations vars' Nothing proof (goals ++ unfocusedGoals) (proofs ++ unfocusedProofs)
            tactic' : _ ->  lift . Left . UnusedTactics $ tacticPos tactic'