{-# LANGUAGE GADTs,FlexibleContexts #-}

-- Imports for Monads

import Control.Monad

-- BBAE AST and Type Definitions

data TBBAE where
  TNum :: TBBAE
  TBool :: TBBAE
  deriving (Show,Eq)

data BBAE where
  Num :: Int -> BBAE
  Plus :: BBAE -> BBAE -> BBAE
  Minus :: BBAE -> BBAE -> BBAE
  Bind :: String -> BBAE -> BBAE -> BBAE
  Id :: String -> BBAE
  Boolean :: Bool -> BBAE
  And :: BBAE -> BBAE -> BBAE
  Leq :: BBAE -> BBAE -> BBAE
  IsZero :: BBAE -> BBAE
  If :: BBAE -> BBAE -> BBAE -> BBAE
  deriving (Show,Eq)

type Env = [(String,BBAE)]

type Cont = [(String,TBBAE)]

-- Exercise 1 - Adding Booleans
-- SUBSTITUTION
subst :: String -> BBAE -> BBAE -> BBAE
subst _ _ (Num n) = Num n
subst i v (Plus l r) = Plus (subst i v l) (subst i v r)
subst i v (Minus l r) = Minus (subst i v l) (subst i v r)
subst i v (Bind i' v' b') = if i==i'
                            then Bind i' (subst i v v') b'
                            else Bind i' (subst i v v') (subst i v b')
subst i v (Id i') = if i==i'
                    then v
                    else Id i'
subst i v (Boolean b) = Boolean b
subst i v (And l r) = And (subst i v l) (subst i v r)
subst i v (Leq l r) = Leq (subst i v l) (subst i v r)
subst i v (IsZero e) = IsZero (subst i v e)
subst i v (If c t e) = If (subst i v c) (subst i v t) (subst i v e)

evalS :: BBAE -> Maybe BBAE
evalS (Num n) = if n >= 0 then Just (Num n) else Nothing
evalS (Plus l r) = do {
  (Num l') <- evalS l;
  (Num r') <- evalS r;
  return (Num (l' + r'))
}
evalS (Minus l r) = do {
  (Num l') <- evalS l;
  (Num r') <- evalS r;
  if l' >= r' then return (Num (l' - r')) else Nothing
}
evalS (Bind i v b) = do {
   v' <- evalS v;
   evalS (subst i v' b)
 }
evalS (Id id) = Nothing
evalS (Boolean b) = Just (Boolean b)
evalS (And l r) = do {
  (Boolean l') <- evalS l;
  (Boolean r') <- evalS r;
  return (Boolean (l' && r'))
}
evalS (Leq l r) = do {
  (Num l') <- evalS l;
  (Num r') <- evalS r;
  return (Boolean (l' <= r'))
}
evalS (IsZero v) = do {
  (Num v') <- evalS v;
  return (Boolean (v' == 0))
}
evalS (If c t e) = do {
  (Boolean c') <- evalS c;
  (if c' then evalS t else evalS e)
}

-- ENVIRONMENT
evalM :: Env -> BBAE -> Maybe BBAE
evalM env (Num n) = if n >= 0 then Just (Num n) else Nothing
evalM env (Plus l r) = do {
  (Num l') <- evalM env l;
  (Num r') <- evalM env r;
  return (Num (l' + r'))
}
evalM env (Minus l r) = do {
  (Num l') <- evalM env l;
  (Num r') <- evalM env r;
  if l' >= r' then return (Num (l' - r')) else Nothing
}
evalM env (Bind i v b) = do {
  v' <- evalM env v;
  evalM ((i,v'):env) b
}
evalM env (Id id) = lookup id env
evalM env (Boolean b) = Just (Boolean b)
evalM env (And l r) = do {
  (Boolean l') <- evalM env l;
  (Boolean r') <- evalM env r;
  return (Boolean (l' && r'))
}
evalM env (Leq l r) = do {
  (Num l') <- evalM env l;
  (Num r') <- evalM env r;
  return (Boolean (l' <= r'))
}
evalM env (IsZero v) = do {
  (Num v') <- evalM env v;
  return (Boolean (v' == 0))
}
evalM env (If c t e) = do {
  (Boolean c') <- evalM env c;
  if c' then evalM env t else evalM env e
}

-- TEST EVALUATORS
testBBAE :: BBAE -> Bool
testBBAE expr = evalS expr == evalM [] expr


-- Exercise 2 - Type Checking
typeofM :: Cont -> BBAE -> Maybe TBBAE
typeofM cont (Num x) = if x >= 0 then Just TNum else Nothing
typeofM cont (Plus l r) = do { l' <- typeofM cont l ;
                              r' <- typeofM cont r ;
                              if l'==TNum && r'==TNum then return TNum else Nothing }
typeofM cont (Minus l r) = do { l' <- typeofM cont l ;
                               r' <- typeofM cont r ;
                               if l'==TNum && r'==TNum then return TNum else Nothing }
typeofM cont (Bind i v b) = do { v' <- typeofM cont v;
                                typeofM ((i,v'):cont) b }
typeofM cont (Id id) = lookup id cont
typeofM cont (Boolean b) = Just TBool
typeofM cont (And l r) = do { TBool <- typeofM cont l ;
                             TBool <- typeofM cont r ;
                             return TBool }
typeofM cont (Leq l r) = do { TNum <- typeofM cont l ;
                             TNum <- typeofM cont r ;
                             return TBool }
typeofM cont (IsZero v) = do { TNum <- typeofM cont v ;
                              return TBool }
typeofM cont (If c t e) = do { TBool <- typeofM cont c ;
                              t' <- typeofM cont t ;
                              e' <- typeofM cont e ;
                              if t'==e' then return t' else Nothing }

evalT :: BBAE -> Maybe BBAE
evalT x = do {
  typeofM [] x;
  evalM [] x
}


-- -- Test cases for evalS
-- evalSTestCases :: [(String, BBAE, Maybe BBAE)]
-- evalSTestCases =
--   [ ("Test 1", Num 42, Just (Num 42))
--   , ("Test 2", Plus (Num 2) (Num 3), Just (Num 5))
--   , ("Test 3", Minus (Num 5) (Num 2), Just (Num 3))
--   , ("Test 4", Bind "x" (Num 5) (Id "x"), Just (Num 5))
--   , ("Test 5", Bind "x" (Num 5) (Plus (Id "x") (Num 3)), Just (Num 8))
--   , ("Test 6", Id "y", Nothing) -- Unbound identifier
--   , ("Test 7", Boolean True, Just (Boolean True))
--   , ("Test 8", And (Boolean True) (Boolean False), Just (Boolean False))
--   , ("Test 9", Leq (Num 5) (Num 5), Just (Boolean True))
--   , ("Test 10", IsZero (Num 0), Just (Boolean True))
--   , ("Test 11", IsZero (Num 42), Just (Boolean False))
--   , ("Test 12", If (Boolean True) (Num 5) (Num 10), Just (Num 5))
--   , ("Test 13", If (Boolean False) (Num 5) (Num 10), Just (Num 10))
--   ]

-- -- Test cases for evalM
-- evalMTestCases :: [(String, Env, BBAE, Maybe BBAE)]
-- evalMTestCases =
--   [ ("Test 14", [], Num 42, Just (Num 42))
--   , ("Test 15", [], Plus (Num 2) (Num 3), Just (Num 5))
--   , ("Test 16", [], Minus (Num 5) (Num 2), Just (Num 3))
--   , ("Test 17", [("x", Num 5)], Id "x", Just (Num 5))
--   , ("Test 18", [("x", Num 3)], Id "x", Just (Num 3))
--   , ("Test 19", [], Id "y", Nothing) -- Unbound identifier
--   , ("Test 20", [], Boolean True, Just (Boolean True))
--   , ("Test 21", [], And (Boolean True) (Boolean False), Just (Boolean False))
--   , ("Test 22", [], Leq (Num 5) (Num 5), Just (Boolean True))
--   , ("Test 23", [], IsZero (Num 0), Just (Boolean True))
--   , ("Test 24", [], IsZero (Num 42), Just (Boolean False))
--   , ("Test 25", [], If (Boolean True) (Num 5) (Num 10), Just (Num 5))
--   , ("Test 26", [], If (Boolean False) (Num 5) (Num 10), Just (Num 10))
--   ]

-- -- Test cases for typeofM and evalT
-- typeofMAndEvalTTestCases :: [(String, BBAE, Maybe TBBAE, Maybe BBAE)]
-- typeofMAndEvalTTestCases =
--   [ ("Test 27", Num 42, Just TNum, Just (Num 42))
--   , ("Test 28", Plus (Num 2) (Num 3), Just TNum, Just (Num 5))
--   , ("Test 29", Plus (Num 2) (Boolean True), Nothing, Nothing)  -- Type mismatch
--   , ("Test 30", Minus (Num 5) (Num 2), Just TNum, Just (Num 3))
--   , ("Test 31", Bind "x" (Num 5) (Id "x"), Just TNum, Just (Num 5))
--   , ("Test 32", Bind "x" (Num 5) (Plus (Id "x") (Num 3)), Just TNum, Just (Num 8))
--   , ("Test 33", Id "y", Nothing, Nothing) -- Unbound identifier
--   , ("Test 34", Boolean True, Just TBool, Just (Boolean True))
--   , ("Test 35", And (Boolean True) (Boolean False), Just TBool, Just (Boolean False))
--   , ("Test 36", Leq (Num 5) (Num 5), Just TBool, Just (Boolean True))
--   , ("Test 37", IsZero (Num 0), Just TBool, Just (Boolean True))
--   , ("Test 38", IsZero (Boolean True), Nothing, Nothing)  -- Type mismatch
--   , ("Test 39", IsZero (Num 42), Just TBool, Just (Boolean False))
--   , ("Test 40", If (Boolean True) (Num 5) (Num 10), Just TNum, Just (Num 5))
--   , ("Test 41", If (Boolean False) (Num 5) (Num 10), Just TNum, Just (Num 10))
--   , ("Test 42", If (Num 0) (Num 5) (Num 10), Nothing, Nothing)  -- Type mismatch
--   ]

-- main :: IO ()
-- main = do
--   putStrLn "\n Running evalS test cases:"
--   mapM_ runEvalSTest evalSTestCases

--   putStrLn "\n Running evalM test cases:"
--   mapM_ runEvalMTest evalMTestCases

--   putStrLn "\n Running typeofM and evalT test cases:"
--   mapM_ runTypeAndEvalTTest typeofMAndEvalTTestCases

--   where
--     runEvalSTest (name, input, expected) = do
--       let result = evalS input
--       putStrLn $ name ++ " (evalS): " ++ show result
--       if result == expected
--         then putStrLn "  Passed"
--         else putStrLn "  Failed"

--     runEvalMTest (name, env, input, expected) = do
--       let result = evalM env input
--       putStrLn $ name ++ " (evalM): " ++ show result
--       if result == expected
--         then putStrLn "  Passed"
--         else putStrLn "  Failed"

--     runTypeAndEvalTTest (name, input, expectedType, expectedResult) = do
--       let resultType = typeofM [] input
--       let result = evalT input
--       putStrLn $ name ++ " (typeofM): " ++ show resultType
--       putStrLn $ name ++ " (evalT): " ++ show result
--       if resultType == expectedType && result == expectedResult
--         then putStrLn "  Passed"
--         else putStrLn "  Failed"