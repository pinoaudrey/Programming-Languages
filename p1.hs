{-# LANGUAGE GADTs, FlexibleContexts #-}

-- Imports for Monads
import Control.Monad
import Distribution.Compat.ResponseFile (expandResponse)

-- AST Definition
data TABE where
  TNum :: TABE
  TBool :: TABE
  deriving (Show,Eq)

data ABE where
  Num :: Int -> ABE
  Plus :: ABE -> ABE -> ABE
  Minus :: ABE -> ABE -> ABE
  Mult :: ABE -> ABE -> ABE
  Div :: ABE -> ABE -> ABE
  Boolean :: Bool -> ABE
  And :: ABE -> ABE -> ABE
  Leq :: ABE -> ABE -> ABE
  IsZero :: ABE -> ABE
  If :: ABE -> ABE -> ABE -> ABE
  deriving (Show,Eq)

-- Evaluation Function
evalM :: ABE -> (Maybe ABE)
evalM (Num n) =
  if n >= 0
    then Just (Num n)
    else Nothing 
evalM (Plus e1 e2) = do
  v1 <- evalM e1
  v2 <- evalM e2
  case (v1, v2) of
    (Num n1, Num n2) -> Just (Num (n1 + n2))
    _ -> Nothing
evalM (Minus e1 e2) = do
  v1 <- evalM e1
  v2 <- evalM e2
  case (v1, v2) of
    (Num n1, Num n2) ->
      if n1 >= n2
        then Just (Num (n1 - n2))
        else Nothing
    _ -> Nothing
evalM (Mult e1 e2) = do
  v1 <- evalM e1
  v2 <- evalM e2
  case (v1, v2) of
    (Num n1, Num n2) -> Just (Num (n1 * n2))
    _ -> Nothing
evalM (Div e1 e2) = do
  v1 <- evalM e1
  v2 <- evalM e2
  case (v1, v2) of
    (Num n1, Num n2) ->
      if n2 /= 0
        then Just (Num (n1 `div` n2))
        else Nothing
    _ -> Nothing
evalM (Boolean b) = Just (Boolean b)
evalM (And e1 e2) = do
  v1 <- evalM e1
  v2 <- evalM e2
  case (v1, v2) of
    (Boolean b1, Boolean b2) -> Just (Boolean (b1 && b2))
    _ -> Nothing
evalM (Leq e1 e2) = do
  v1 <- evalM e1
  v2 <- evalM e2
  case (v1, v2) of
    (Num n1, Num n2) -> Just (Boolean (n1 <= n2))
    _ -> Nothing
evalM (IsZero e) = do
  v <- evalM e
  case v of
    (Num n) -> Just (Boolean (n == 0))
    _ -> Nothing
evalM (If cond e1 e2) = do
  vCond <- evalM cond
  case vCond of
    (Boolean True) -> evalM e1
    (Boolean False) -> evalM e2
    _ -> Nothing

-- Type Derivation Function
typeofM :: ABE -> Maybe TABE
typeofM (Num _) = Just TNum
typeofM (Plus e1 e2) = do
  t1 <- typeofM e1
  t2 <- typeofM e2
  case (t1, t2) of
    (TNum, TNum) -> Just TNum
    _ -> Nothing 
typeofM (Minus e1 e2) = do
  t1 <- typeofM e1
  t2 <- typeofM e2
  case (t1, t2) of
    (TNum, TNum) -> Just TNum
    _ -> Nothing 
typeofM (Mult e1 e2) = do
  t1 <- typeofM e1
  t2 <- typeofM e2
  case (t1, t2) of
    (TNum, TNum) -> Just TNum
    _ -> Nothing 
typeofM (Div e1 e2) = do
  t1 <- typeofM e1
  t2 <- typeofM e2
  case (t1, t2) of
    (TNum, TNum) -> Just TNum
    _ -> Nothing 
typeofM (Boolean _) = Just TBool
typeofM (And e1 e2) = do
  t1 <- typeofM e1
  t2 <- typeofM e2
  case (t1, t2) of
    (TBool, TBool) -> Just TBool
    _ -> Nothing 
typeofM (Leq e1 e2) = do
  t1 <- typeofM e1
  t2 <- typeofM e2
  case (t1, t2) of
    (TNum, TNum) -> Just TBool
    _ -> Nothing 
typeofM (IsZero e) = do
  t <- typeofM e
  case t of
    TNum -> Just TBool
    _ -> Nothing 
typeofM (If cond e1 e2) = do
  tCond <- typeofM cond
  t1 <- typeofM e1
  t2 <- typeofM e2
  case (tCond, t1, t2) of
    (TBool, t1', t2')
      | t1' == t2' -> Just t1'
    _ -> Nothing 

-- Combined Interpreter
evalTypeM :: ABE -> Maybe ABE
evalTypeM expr = do
  _ <- typeofM expr
  evalM expr

-- Optimizer
optimize :: ABE -> ABE
optimize (Num n) = Num n
optimize (Boolean b) = Boolean b
optimize (Plus l r) = if optimize r == Num 0 then optimize l else Plus (optimize l) (optimize r)
optimize (If c t e) = if c==Boolean True then optimize t else (if c==Boolean False then optimize e else If (optimize c) (optimize t) (optimize e))
optimize x = x

evalOptM :: ABE -> Maybe ABE
evalOptM expr = evalM (optimize expr)

