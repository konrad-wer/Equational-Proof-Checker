module Parser
    ( parseTheory
    ) where

-- "You've never heard of the Millennium Falcon?
-- …It's the ship that made the Kessel Run in less than 0.000012 megaParsecs."

import Data.Void
import Control.Monad
import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import Control.Monad.Combinators.Expr
import qualified Data.Set as Set
import qualified Data.Map as Map
import AST

type Parser = Parsec Void String

sc :: Parser ()
sc = L.space space1 lineCmnt blockCmnt
  where
    lineCmnt  = L.skipLineComment "//"
    blockCmnt = L.skipBlockComment "/*" "*/"

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: String -> Parser String
symbol = L.symbol sc

symbolWithPos :: String -> Parser (SourcePos, String)
symbolWithPos x = do
  pos <- getSourcePos
  sym <- symbol x
  return (pos, sym)

comma :: Parser String
comma = symbol ","

unsignedInteger :: Parser Int
unsignedInteger = lexeme L.decimal

stringLiteral :: Parser String
stringLiteral = lexeme $ char '\"' *> manyTill L.charLiteral (char '\"')

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

braces :: Parser a -> Parser a
braces = between (symbol "{") (symbol "}")

angles :: Parser a -> Parser a
angles = between (symbol "<") (symbol ">")

brackets :: Parser a -> Parser a
brackets = between (symbol "[") (symbol "]")

rword :: String -> Parser ()
rword w = (lexeme . try) (string w *> notFollowedBy alphaNumChar)

rws :: [String]
rws = ["Theory", "=", "/"]

identifier :: Parser Var
identifier = (lexeme . try) (p >>= check)
  where
    p = (:) <$> alphaNumChar <*> many (alphaNumChar <|> char '_')
    check x
      | x `elem` rws = fail $ "keyword " ++ show x ++ " cannot be an identifier"
      | otherwise = return x

-- Theory syntax ---------------------------------------------------------------

parseTheory :: String -> String -> Either (ParseErrorBundle String Void) Theory
parseTheory = parse (between sc eof theory)

theory :: Parser Theory
theory = do
  rword "Theory"
  name <- option Nothing (Just <$> identifier)
  signature <- Map.fromList <$> parens (sig `sepBy` symbol ",")
  Theory name signature <$> braces (equation signature `sepBy` symbol ",")

-- named 'sig' instead of 'signature', because name 'signature'
-- causes syntax highlighting to break
sig :: Parser  (Var, Int)
sig = do
  sym <- identifier
  symbol "/"
  arity <- unsignedInteger
  return (sym, arity)

equation :: Map.Map Var Int -> Parser Equation
equation functionSymbols = do
  l <- term functionSymbols
  symbol "="
  r <- term functionSymbols
  return $ Equation (Set.union (freeVarsOfTerm l) (freeVarsOfTerm r)) l r

term :: Map.Map Var Int -> Parser Term
term functionSymbols = do
  pos <- getSourcePos
  id <- identifier
  case Map.lookup id functionSymbols of
    Nothing -> return $ Var id
    Just arity -> do
      args <- parens $ sepBy (term functionSymbols) (symbol ",")
      if length args == arity then
        return $ FunctionSymbol id args
      else
        fail $ "Mismatched arity at: " ++ sourcePosPretty pos

