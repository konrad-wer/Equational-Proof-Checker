module Main where

import System.Environment
import Text.Megaparsec.Error (errorBundlePretty)
import System.Exit
import Data.List
import Data.Maybe
import Parser

printHelp :: IO ()
printHelp = putStrLn $ "Usage: kwoka filename [options]\n" ++
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
  if length filenames /= 1 || any (not . flip elem ["-debug", "-help"]) args then do
    printHelp
    exitWith $ ExitFailure 1
  else
    return (head filenames, args)

main :: IO ()
main = do
  (filename, args) <- parseArgs . snd . fromMaybe ("", []) . uncons =<< getArgs
  if "-help" `elem` args then
    printHelp
  else do
    sourceCode <- readFile filename
    case parseTheory filename sourceCode of
      Left err -> putStrLn $ errorBundlePretty err
      Right ast -> print ast
