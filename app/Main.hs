module Main where

import System.Environment
import System.IO
import Text.Megaparsec.Error (errorBundlePretty)
import Text.Megaparsec.Pos
import System.Exit
import Data.List
import Control.Monad
import qualified Data.Map as Map
import Data.Maybe
import Parser
import AST
import ProofChecker

printHelp :: IO ()
printHelp = putStrLn $ "Usage: EquationalProofChecker filename [options]\n" ++
  "Options:\n" ++
  "-debug - Pretty print program with inferred types to file\n" ++
  "-help - Print this message\n"

isArg :: String -> Bool
isArg ('-' : _) = True
isArg _ = False

parseArgs :: [String] -> IO (String, [String])
parseArgs xs = do
  let filenames = filter (not . isArg) xs
  let args = filter isArg xs
  if length filenames /= 1 || not (all (`elem` ["-debug", "-help"]) args) then do
    printHelp
    exitWith $ ExitFailure 1
  else
    return (head filenames, args)

addEquationToTheory :: Theory -> Var -> Equation -> Theory
addEquationToTheory (Theory theoryName sig equations) name equation =
  Theory theoryName sig $ Map.insert name equation equations

findAndDebug :: Var -> Theory -> [Theorem SourcePos] -> IO ()
findAndDebug _ _ [] = putStrLn "No such theorem!"
findAndDebug proofForDebug theory (Theorem _ name equation proof : theorems)
  | proofForDebug == name = do
    putStrLn "================ Debug start ================"
    debug theory equation proof
  | otherwise =
    case check theory equation proof of
      Right _ -> putStrLn (name ++ ": OK!\n") >>
        findAndDebug proofForDebug (addEquationToTheory theory name equation) theorems
      Left error -> putStrLn (name ++ ":\n" ++ show error ++ "\n") >>
        findAndDebug proofForDebug theory theorems

main :: IO ()
main = do
  (filename, args) <- parseArgs =<< getArgs
  if "-help" `elem` args then
    printHelp
  else do
    sourceCode <- readFile filename
    case parse filename sourceCode of
      Left err -> putStrLn $ errorBundlePretty err
      Right (Session theory theorems) ->
        if "-debug" `elem` args then do
          putStrLn "Name of theorem for debugging:"
          proofForDebug <- getLine
          findAndDebug proofForDebug theory theorems
        else
          foldM_ (\theory' (Theorem _ name equation proof) ->
            case check theory' equation proof of
              Right _ -> putStrLn (name ++ ": OK!\n") >> return (addEquationToTheory theory' name equation)
              Left error -> putStrLn (name ++ ":\n" ++ show error ++ "\n") >> return theory') theory theorems
