module Parser (parse_expr, parse_code) where

import Control.Monad
import Control.Applicative
import Expr
import Control.Applicative (Alternative(..))
import Data.Char (isAlpha, isSpace, isAlphaNum)


-- Parser data type
newtype Parser a = Parser {
    parse :: String -> Maybe(a, String)
}

--- type declaration ---

instance Functor Parser where
    fmap f (Parser p) = Parser $ \input -> do
        (result, rest) <- p input
        Just (f result, rest)

instance Applicative Parser where
    pure x = Parser $ \input -> Just (x, input)
    (Parser p1) <*> (Parser p2) = Parser $ \input -> do
        (f, rest1) <- p1 input
        (x, rest2) <- p2 rest1
        Just (f x, rest2)

instance Alternative Parser where
    empty = Parser $ const Nothing
    (Parser p1) <|> (Parser p2) = Parser $ \input -> p1 input <|> p2 input

instance Monad Parser where
    (Parser p) >>= f = Parser $ \input -> do
        (result, rest) <- p input
        parse (f result) rest

satisfy :: (Char -> Bool) -> Parser Char
satisfy predicate = Parser $ \input ->
    case input of
        c:rest | predicate c -> Just (c, rest)
        _ -> Nothing

char :: Char -> Parser Char
char c = satisfy (== c)

string :: String -> Parser String
string "" = pure ""
string (c:cs) = (:) <$> char c <*> string cs

spaces :: Parser ()
spaces = () <$ many (satisfy isSpace)

variable :: Parser Expr
variable = do
  isMacro <- optional1 (char '$')
  case isMacro of
    Just _ -> Macro <$> name
    Nothing -> Variable <$> name
  where
    name :: Parser String
    name = some (satisfy isAlpha)


function :: Parser Expr
function = do
  char '\\'
  spaces
  vars <- variable `sepBy` (char ',')
  spaces
  char '.'
  spaces
  body <- atom <|> parenthesizedExpr
  case vars of
    [] -> pure body
    _ -> foldr (\v acc -> Function (getVarName v) <$> acc) (pure body) vars

parenthesizedExpr :: Parser Expr
parenthesizedExpr = do
  char '('
  spaces
  expr <- expr
  spaces
  char ')'
  pure expr

sepBy :: Parser a -> Parser sep -> Parser [a]
sepBy p sep = (:) <$> p <*> many (sep *> p) <|> pure []

optional1 :: Parser a -> Parser (Maybe a)
optional1 p = (Just <$> p) <|> pure Nothing

application :: Parser Expr
application = do
    expr1 <- atom
    applicationRest expr1
  where
    applicationRest :: Expr -> Parser Expr
    applicationRest exprSoFar = do
        spaces
        mbExpr <- optional1 atom
        case mbExpr of
            Just expr -> applicationRest (Application exprSoFar expr)
            Nothing -> return exprSoFar

atom :: Parser Expr
atom = variable <|> function <|> (char '(' *> spaces *> expr <* spaces <* char ')')

macro1 :: Parser Expr
macro1 = do
    _ <- char '$'
    name <- some (satisfy isAlpha)
    pure (Macro name)

expr :: Parser Expr
expr = application <|> atom

getVarName :: Expr -> String
getVarName (Variable name) = name
getVarName _ = ""

parse_expr :: String -> Expr
parse_expr input =
            case parse expr input of
                Just (result, "") -> result
                _ -> Variable "123"
        
-- TODO 4.2. parse code
parse_code :: String -> Code
parse_code input =
    case parse codeParser input of
           Just (result, "") -> result
           _ -> case parse exprParser input of
                  Just (expr, "") -> Evaluate expr
                  _ -> Evaluate (Variable "123")


codeParser :: Parser Code
codeParser = assignParser <|> evaluateParser

assignParser :: Parser Code
assignParser = do
  varName <- spaces *> identifier <* spaces <* char '=' <* spaces
  lambdaExpr <- exprParser
  return (Assign varName lambdaExpr)

evaluateParser :: Parser Code
evaluateParser = Evaluate <$> exprParser

identifier :: Parser String
identifier = some (satisfy isAlphaNum)

exprParser :: Parser Expr
exprParser = application <|> atom
