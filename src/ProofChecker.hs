{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ExistentialQuantification #-}

module ProofChecker where

import AST
import Control.Monad.State
import Control.Monad.Trans
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Maybe
import Data.List (intercalate)
import Text.Megaparsec.Pos

type Subst k = Map.Map Var (Term k)

data ProofStatus p
  = Finished (Subst Open)
  | InProgress (Term Open) (Term Open) (Subst Open)
  | NewGoals [(Term Open, Term Open)] [Proof p]

instance SourcePos ~ p => Show (ProofStatus p) where
  show (Finished _) = "Goal complete!"
  show (InProgress t1 t2 _) = show t1 ++ " = " ++ show t2
  show (NewGoals goals _) =
    let (goalsL, goalsR) = unzip goals in
    "New goals:\n" ++ intercalate "\n" (zipWith (\l r -> " - " ++ show l ++ " = " ++ show r) goalsL goalsR)

data ProofError p where
  ReflexivityError :: p -> Term k1 -> Term k2 -> ProofError p
  UndefinedVariableError :: p -> Var -> ProofError p
  UnfinishedProof :: Term k1 -> Term k2 -> ProofError p
  UnusedTactics :: p -> ProofError p
  CongruenceError :: p -> Term k1 -> Term k2 -> ProofError p
  ApplicationError :: p  -> Term k1 -> Term k2 -> Term k3 -> Term k4 -> ProofError p
  EquationDoesNotExistError :: p -> Var -> ProofError p
  WrongNumberOfSubproofsError :: p -> Int -> Int -> ProofError p

instance SourcePos ~ p => Show (ProofError p) where
  show (ReflexivityError p t1 t2) = sourcePosPretty p ++ "\nReflexivity failure: terms are not equal: " ++
    show t1 ++ " =/= " ++ show t2
  show (UndefinedVariableError p x) = sourcePosPretty p ++ "\nVariable not in scope: " ++ x
  show (UnfinishedProof t1 t2) = "Unfinished proof: " ++ show t1 ++ " = " ++ show t2
  show (UnusedTactics p) = sourcePosPretty p ++ "\nUnused tactics left"
  show (CongruenceError p t1 t2) = sourcePosPretty p ++ "\nCould not apply congruence to terms: " ++
    show t1 ++ ", " ++ show t2
  show (ApplicationError p eq1 eq2 t1 t2) = sourcePosPretty p ++ "\nCould not apply equation: " ++
    show eq1 ++ " = " ++ show eq2 ++ ", to the goal: " ++ show t1 ++ " = " ++ show t2
  show (EquationDoesNotExistError p eqName) = sourcePosPretty p ++ "\nEquation " ++ eqName ++ " does not exist."
  show (WrongNumberOfSubproofsError p expected actual) = sourcePosPretty p ++
    "\nWrong number of subproofs. Expected " ++ show expected ++ ", but found: " ++ show actual


type ProofState p = StateT Int (Either (ProofError p))

reflexivity :: p -> Term Open -> Term Open -> ProofState p (ProofStatus p)
reflexivity pos t1 t2 =
  case tryUnify t1 t2 of
    Just s -> return $ Finished s
    Nothing -> lift . Left $ ReflexivityError pos t1 t2

congruence :: p -> Term Open -> Term Open -> [Proof p] -> ProofState p (ProofStatus p)
congruence pos t1@(FunctionSymbol f args) t2@(FunctionSymbol g args') subproofs
  | f == g && length args == length args' =
    if length args == length subproofs then
      return $ NewGoals (zip args args') subproofs
    else
      lift . Left $ WrongNumberOfSubproofsError pos (length args) (length subproofs)
  | otherwise = lift . Left $ CongruenceError pos t1 t2
congruence pos t1 t2 _ = lift . Left $ CongruenceError pos t1 t2

isTermWellFounded :: p -> Set.Set Var -> Term Closed -> ProofState p ()
isTermWellFounded pos vars (Var x)
  | x `Set.member` vars = return ()
  | otherwise = lift . Left $ UndefinedVariableError pos x
isTermWellFounded pos vars (FunctionSymbol _ args) =
  mapM_ (isTermWellFounded pos vars) args

freshVar :: ProofState p String
freshVar = do
  n <- get
  modify (+1)
  return ("#" ++ show n)

openTerm :: Term Closed -> Term Open
openTerm (Var x) = Var x
openTerm (FunctionSymbol f args) = FunctionSymbol f $ openTerm <$> args

checkBindings :: p -> Set.Set Var -> Set.Set Var -> Map.Map Var (Term Closed) -> ProofState p (Set.Set Var)
checkBindings pos equationVars termVars bindings = do
  mapM_ (isTermWellFounded pos termVars) bindings
  let boundVars = Set.fromList (Map.keys bindings)
  case Set.toList (boundVars `Set.difference` equationVars) of
    [] -> return (equationVars `Set.difference` boundVars)
    x : _ -> lift . Left $ UndefinedVariableError pos x

openWithFreshVars :: p -> Set.Set Var -> Map.Map Var (Term Closed) -> Equation -> ProofState p (Term Open, Term Open)
openWithFreshVars pos termVars bindings (Equation vars t1 t2) = do
  varList <- Set.toList <$> checkBindings pos vars termVars bindings
  let bindingSubst = Map.map openTerm bindings
  newVars <- mapM (fmap UnificationVar . const freshVar) varList
  let subst = Map.fromList (zip varList newVars) `Map.union` bindingSubst
  return (applySubst subst t1, applySubst subst t2)

applySubst :: Subst Open -> Term k -> Term Open
applySubst subst (Var x) = fromMaybe (Var x) (Map.lookup x subst)
applySubst subst (UnificationVar x) = fromMaybe (UnificationVar x) (Map.lookup x subst)
applySubst subst (FunctionSymbol f args) = FunctionSymbol f $ applySubst subst <$> args

composeSubsts :: Subst Open -> Subst Open -> Subst Open
composeSubsts s2 s1 =
  let s1' = Map.map (applySubst s2) s1 in
  Map.union s1' s2

tryUnify :: Term Open -> Term Open -> Maybe (Subst Open)
tryUnify (Var x) (Var y)
  | x == y = Just Map.empty
  | otherwise = Nothing
tryUnify (UnificationVar x) t =
  Just $ Map.singleton x t
tryUnify t (UnificationVar x) =
  Just $ Map.singleton x t
tryUnify (FunctionSymbol f args) (FunctionSymbol g args')
  | f == g = foldM (\subst (t1, t2) -> do
      let t1' = applySubst subst t1
      subst' <- tryUnify t1' t2
      return $ subst' `composeSubsts` subst)
    Map.empty $ zip args args'
  | otherwise = Nothing
tryUnify _ _ = Nothing

findAndRewrite :: Term Open -> Term Open -> Term Open -> (Subst Open, Term Open)
findAndRewrite tFrom tTo t =
  case tryUnify tFrom t of
    Just s -> (s, applySubst s tTo)
    Nothing -> case t of
      FunctionSymbol f args ->
          let (s, args') = foldl (\(subst, ts) t ->
                let t' = applySubst subst t in
                let (subst', t'') = findAndRewrite tFrom tTo t' in
                (subst' `composeSubsts` subst, ts ++ [applySubst subst' t'']))
                (Map.empty, []) args in
          (s, FunctionSymbol f args')
      _ -> (Map.empty, t)

rewrite :: Side -> Term Open -> Term Open -> Term Open -> Term Open -> ProofState p (ProofStatus p)
rewrite BothSides from to t1 t2 = do
  let (s1, t1') = findAndRewrite from to t1
  let (s2, t2') = findAndRewrite from to (applySubst s1 t2)
  let s = s2 `composeSubsts` s1
  let t1'' = applySubst s t1'
  let t2'' = applySubst s t2'
  return $ InProgress t1'' t2'' s
rewrite LeftSide from to t1 t2 = do
  let (s, t1') = findAndRewrite from to t1
  let t1'' = applySubst s t1'
  let t2'' = applySubst s t2
  return $ InProgress t1'' t2'' s
rewrite RightSide from to t1 t2 = do
  let (s, t2') = findAndRewrite from to t2
  let t1'' = applySubst s t1
  let t2'' = applySubst s t2'
  return $ InProgress t1'' t2'' s

apply :: p -> Term Open -> Term Open -> Term Open -> Term Open -> ProofState p (ProofStatus p)
apply p eq1 eq2 t1 t2 =
  case tryUnify eq1 t1 of
    Nothing -> lift . Left $ ApplicationError p eq1 eq2 t1 t2
    Just s1 -> do
      let t2' = applySubst s1 t2
      let eq2' = applySubst s1 eq2
      case tryUnify eq2' t2' of
        Nothing -> lift . Left $ ApplicationError p eq1 eq2 t1 t2
        Just s2 -> return $ Finished $ s2 `composeSubsts` s1

proofStep :: Theory -> Set.Set Var -> Term Open -> Term Open -> Tactic p -> ProofState p (ProofStatus p)
proofStep _ _ t1 t2 (Reflexivity pos) = reflexivity pos t1 t2
proofStep _ _ t1 t2 (Symmetry _) = return $ InProgress t2 t1 Map.empty
proofStep _ _ t1 t2 (Congruence pos subproofs) = congruence pos t1 t2 subproofs
proofStep _ vars t1 t2 (Transitivity pos t proof1 proof2) = do
  isTermWellFounded pos vars t
  let t' = openTerm t
  return $ NewGoals [(t1, t'), (t', t2)] [proof1, proof2]
proofStep (Theory _ _ equations) vars t1 t2 (RewriteLR p side eqName bindings) =
  case Map.lookup eqName equations of
    Nothing -> lift . Left $ EquationDoesNotExistError p eqName
    Just equation -> do
      (from, to) <- openWithFreshVars p vars bindings equation
      rewrite side from to t1 t2
proofStep (Theory _ _ equations) vars t1 t2 (RewriteRL p side eqName bindings) =
  case Map.lookup eqName equations  of
    Nothing -> lift . Left $ EquationDoesNotExistError p eqName
    Just equation -> do
      (to, from) <- openWithFreshVars p vars bindings equation
      rewrite side from to t1 t2
proofStep (Theory _ _ equations) vars t1 t2 (Apply p eqName) =
  case Map.lookup eqName equations  of
    Nothing -> lift . Left $ EquationDoesNotExistError p eqName
    Just equation -> do
      (l, r) <- openWithFreshVars p vars Map.empty equation
      apply p l r t1 t2

applySubstOnGoal :: Subst 'Open -> (Term Open, Term Open) -> (Term Open, Term Open)
applySubstOnGoal s (l, r) = (applySubst s l, applySubst s r)

check :: Theory -> Equation -> Proof p -> Either (ProofError p) ()
check theory (Equation vars term1 term2) proof =
  flip evalStateT 0 $ chk theory (Just (openTerm term1, openTerm term2)) proof [] []
  where
    chk ::
      Theory ->
      Maybe (Term Open, Term Open) -> Proof p ->
      [(Term Open, Term Open)] -> [Proof p] -> ProofState p ()
    chk equations Nothing [] [] [] = return ()
    chk equations Nothing [] (goal : unfocusedGoals) (proof : unfocusedProofs) =
      chk equations (Just goal) proof unfocusedGoals unfocusedProofs
    chk equations Nothing (tactic : _) _ _ = lift . Left . UnusedTactics $ tacticPos tactic
    chk equations (Just (t1, t2)) [] unfocusedGoals unfocusedProofs =
      lift . Left $ UnfinishedProof t1 t2
    chk equations (Just (t1, t2)) (tactic : proof) unfocusedGoals unfocusedProofs = do
      stepRes <- proofStep theory vars t1 t2 tactic
      case stepRes of
        Finished subst ->
          chk equations Nothing proof (map (applySubstOnGoal subst) unfocusedGoals) unfocusedProofs
        InProgress t1 t2 subst ->
          chk equations (Just (t1, t2)) proof (map (applySubstOnGoal subst) unfocusedGoals) unfocusedProofs
        NewGoals goals proofs ->
          case proof of
            [] -> chk equations Nothing proof (goals ++ unfocusedGoals) (proofs ++ unfocusedProofs)
            tactic' : _ ->  lift . Left . UnusedTactics $ tacticPos tactic'

type DebugProofState = StateT Int IO

debug :: Theory -> Equation -> Proof SourcePos -> IO ()
debug theory (Equation vars term1 term2) proof = do
  putStrLn $ show term1 ++ " = " ++ show term2 ++ "\n"
  flip evalStateT 0 $ dbg theory (Just (openTerm term1, openTerm term2)) proof [] []
  where
    dbg ::
      Theory ->
      Maybe (Term Open, Term Open) -> Proof SourcePos ->
      [(Term Open, Term Open)] -> [Proof SourcePos] -> DebugProofState ()
    dbg equations Nothing [] [] [] = return ()
    dbg equations Nothing [] (goal@(l, r) : unfocusedGoals) (proof : unfocusedProofs) = do
      lift . putStr $ "Starting goal: "
      lift . putStrLn $ show l ++ " = " ++ show r ++ "\n"
      dbg equations (Just goal) proof unfocusedGoals unfocusedProofs
    dbg equations Nothing (tactic : _) _ _ = lift . print . UnusedTactics $ tacticPos tactic
    dbg equations (Just (t1, t2)) [] unfocusedGoals unfocusedProofs =
      lift . print $ UnfinishedProof t1 t2
    dbg equations (Just (t1, t2)) (tactic : proof) unfocusedGoals unfocusedProofs = do
      lift . putStrLn $ "====[ " ++ show tactic ++ " ]===>\n"
      st <- get
      case flip runStateT st $  proofStep theory vars t1 t2 tactic of
        Left err -> lift $ print err
        Right (stepRes, st') -> do
          put st'
          lift $ print stepRes
          void . lift $ getLine
          case stepRes of
            Finished subst ->
              dbg equations Nothing proof (map (applySubstOnGoal subst) unfocusedGoals) unfocusedProofs
            InProgress t1 t2 subst ->
              dbg equations (Just (t1, t2)) proof (map (applySubstOnGoal subst) unfocusedGoals) unfocusedProofs
            NewGoals goals proofs ->
              case proof of
                [] -> dbg equations Nothing proof (goals ++ unfocusedGoals) (proofs ++ unfocusedProofs)
                tactic' : _ ->  lift . print . UnusedTactics $ tacticPos tactic'