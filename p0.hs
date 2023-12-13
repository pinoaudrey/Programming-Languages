{-# LANGUAGE GADTs, FlexibleContexts #-}

-- Imports for Parsec
import Control.Monad
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Language
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Token

--
-- Simple caculator over naturals with no identifiers
--
-- Author: Perry Alexander
-- Date: Tue Jan 23 17:54:44 CST 2018
--
-- Source files for the Arithmetic Expressions (AE) language from PLIH
--

-- AST Definition

data AE where
  Nat :: Int -> AE
  Plus :: AE -> AE -> AE
  Minus :: AE -> AE -> AE
  Mult :: AE -> AE -> AE
  Div :: AE -> AE -> AE
  If0 :: AE -> AE -> AE -> AE
  deriving (Show,Eq)

-- AE Parser (Requires ParserUtils and Parsec included above)

languageDef =
  javaStyle { identStart = letter
            , identLetter = alphaNum
            , reservedNames = [ "if0"
                              , "then"
                              , "else"
                              ]
            , reservedOpNames = [ "+","-","*","/"]
            }
  
lexer = makeTokenParser languageDef

inFix o c a = (Infix (reservedOp lexer o >> return c) a)
preFix o c = (Prefix (reservedOp lexer o >> return c))
postFix o c = (Postfix (reservedOp lexer o >> return c))

parseString p str =
  case parse p "" str of
    Left e -> error $ show e
    Right r -> r

expr :: Parser AE
expr = buildExpressionParser operators term

operators = [
  [ inFix "*" Mult AssocLeft
    , inFix "/" Div AssocLeft ]
  , [ inFix "+" Plus AssocLeft
  , inFix "-" Minus AssocLeft ]
  ]
  
numExpr :: Parser AE
numExpr = do i <- integer lexer
             return (Nat (fromInteger i))

ifExpr :: Parser AE
ifExpr  = do reserved lexer "if0"
             c <- expr
             reserved lexer "then"
             t <- expr
             reserved lexer "else"
             e <- expr
             return (If0 c t e)
                     

term = parens lexer expr
       <|> numExpr
       <|> ifExpr

-- Parser invocation
-- Call parseAE to parse a string into the AE data structure.

parseAE = parseString expr

-- Evaluation Functions
-- Replace the bodies of these functions with your implementations for
-- Exercises 1-4.  Feel free to add utility functions or testing functions as
-- you see fit, but do not change the function signatures.  Note that only
-- Exercise 4 requires you to integrate the parser above.

-- ************** Exercise 1 **************
-- Write a function, evalAE::AE -> Int, that takes a AE data structure, evaluates it, and returns an Int. 
-- If your interpreter fails, it should throw an error using the error function discussed in class.
evalAE :: AE -> Int
evalAE (Nat n) = if n < 0 then error "!" else n
evalAE (Plus l r) = (evalAE l) + (evalAE r)
evalAE (Minus l r) = let x = (evalAE l) - (evalAE r) in
                     if x < 0 then error "!" else x
evalAE (Mult l r) = (evalAE l) * (evalAE r)
evalAE (Div l r) = let x = (evalAE l) `div` (evalAE r) in
                   if x < 0 then error "!" else x
evalAE (If0 c t e) = if (evalAE c) == 0 then (evalAE t) else (evalAE e)

-- ************** Exercise 2 **************
-- Write a function, evalAEMaybe::AE -> Maybe Int, that takes the same AE data structure as Exercise 1, evalutes it, and returns a value. 
-- Use Just to return a number and Nothing to indicate an error. Do not use Maybe as a monad in this interpreter. 
-- Use if and/or case to process errors.
evalAEMaybe :: AE -> Maybe Int
evalAEMaybe (Nat n) = if n < 0 then Nothing else Just n
-- Plus 
evalAEMaybe (Plus l r) = case evalAEMaybe l of
                          Nothing -> Nothing
                          Just l' -> case evalAEMaybe r of
                                        Nothing -> Nothing
                                        Just r' -> Just (l' + r')
-- Minus
evalAEMaybe (Minus l r) = case evalAEMaybe l of
                            Nothing -> Nothing
                            Just l' -> case evalAEMaybe r of
                                            Nothing -> Nothing
                                            Just r' -> if l' < r' then Nothing else Just (l' - r')
-- Multiply
evalAEMaybe (Mult l r) = case evalAEMaybe l of
                            Nothing -> Nothing
                            Just l' -> case evalAEMaybe r of
                                            Nothing -> Nothing
                                            Just r' -> Just (l' * r')
-- Divide
evalAEMaybe (Div l r) = case evalAEMaybe l of
                            Nothing -> Nothing
                            Just l' -> case evalAEMaybe r of
                                            Nothing -> Nothing
                                            Just r' -> if r' == 0 then Nothing else Just (l' `div` r')
evalAEMaybe (If0 c t e) = case evalAEMaybe c of
                            Nothing -> Nothing
                            Just 0 -> evalAEMaybe t
                            Just c' -> evalAEMaybe e

-- ************** Exercise 3 **************
-- Write a function, evalM::AE -> Maybe Int, that takes the same AE data structure as Exercises 1 & 2, evaluates it, and returns a number. 
-- This time, use the do notation to treat Maybe as a monad.
evalM :: AE -> Maybe Int
evalM (Nat n) = do { if n < 0 then Nothing else return n }
evalM (Plus l r) = do { x <- evalM l;
                        y <- evalM r;
                        return (x + y) }
evalM (Minus l r) = do { x <- evalM l;
                        y <- evalM r;
                        if x < y then Nothing else return (x - y) }
evalM (Mult l r) = do { x <- evalM l;
                        y <- evalM r;
                        if x*y < 0 then Nothing else return (x*y) }
evalM (Div l r) = do { x <- evalM l;
                        y <- evalM r;
                        if x `div` y < 0 then Nothing else return (x `div` y) }
evalM (If0 c t e) = do { condition <- evalM c;
                        if condition == 0 then evalM t else evalM e}

-- ************** Exercise 4 **************
-- Write a function, interpAE that combines the AE parser and evalM into a single operation that parses and then evaluates an AE expression. 
-- You will be provided a parser and must integrate it with your interpreter.
interpAE :: String -> Maybe Int
interpAE x = evalM (parseAE x)