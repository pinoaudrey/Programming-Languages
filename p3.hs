{-# LANGUAGE GADTs #-}

-- Imports for Monads

import Control.Monad
-- import Main (evalS)

-- FAE AST and Type Definitions
-- ======================== EXERCISE 1 ========================
data FAE where
  Num :: Int -> FAE
  Plus :: FAE -> FAE -> FAE
  Minus :: FAE -> FAE -> FAE
  Lambda :: String -> FAE -> FAE
  App :: FAE -> FAE -> FAE
  Id :: String -> FAE
  deriving (Show,Eq)

type Env = [(String,FAE)]

evalDynFAE :: Env -> FAE -> (Maybe FAE)
evalDynFAE env (Num n) = if n >= 0 then Just (Num n) else Nothing
evalDynFAE env (Plus l r) = do {
  (Num l') <- evalDynFAE env l;
  (Num r') <- evalDynFAE env r;
  return (Num (l' + r'))
}
evalDynFAE env (Minus l r) = do {
  (Num l') <- evalDynFAE env l;
  (Num r') <- evalDynFAE env r;
  if l' >= r' then return (Num (l' - r')) else Nothing
}
evalDynFAE env (Lambda i b) = Just (Lambda i b)
evalDynFAE env (App f a) = do {
  (Lambda i b) <- evalDynFAE env f;
    a' <- evalDynFAE env a;
  evalDynFAE ((i,a'):env) b
}
evalDynFAE env (Id i) = lookup i env

-- ======================== EXERCISE 2 ========================
data FAEValue where
  NumV :: Int -> FAEValue
  ClosureV :: String -> FAE -> Env' -> FAEValue
  deriving (Show,Eq)
  
type Env' = [(String,FAEValue)]

evalStatFAE :: Env' -> FAE -> (Maybe FAEValue)
evalStatFAE env (Num n) = if n >= 0 then Just (NumV n) else Nothing
evalStatFAE env (Plus l r) = do {
  (NumV l') <- evalStatFAE env l;
  (NumV r') <- evalStatFAE env r;
  return (NumV (l' + r'))
}
evalStatFAE env (Minus l r) = do {
  (NumV l') <- evalStatFAE env l;
  (NumV r') <- evalStatFAE env r;
  if l' >= r' then return (NumV (l' - r')) else Nothing
}
evalStatFAE env (Lambda i b) = Just (ClosureV i b env)
evalStatFAE env (App f a) = do {
  (ClosureV i b env') <- evalStatFAE env f;
  a' <- evalStatFAE env a;
  evalStatFAE ((i,a'):env') b
}
evalStatFAE env (Id i) = lookup i env

-- FBAE AST and Type Definitions

-- ======================== EXERCISE 3 ========================
data FBAE where
  NumD :: Int -> FBAE
  PlusD :: FBAE -> FBAE -> FBAE
  MinusD :: FBAE -> FBAE -> FBAE
  LambdaD :: String -> FBAE -> FBAE
  AppD :: FBAE -> FBAE -> FBAE
  BindD :: String -> FBAE -> FBAE -> FBAE
  IdD :: String -> FBAE
  deriving (Show,Eq)

elabFBAE :: FBAE -> FAE
elabFBAE (NumD n) = Num n
elabFBAE (PlusD l r) = Plus (elabFBAE l) (elabFBAE r)
elabFBAE (MinusD l r) = Minus (elabFBAE l) (elabFBAE r)
elabFBAE (LambdaD i b) = Lambda i (elabFBAE b)
elabFBAE (AppD f a) = App (elabFBAE f) (elabFBAE a)
elabFBAE (BindD i v b) = App (Lambda i (elabFBAE b)) (elabFBAE v)
elabFBAE (IdD i) = Id i

evalFBAE :: Env' -> FBAE -> (Maybe FAEValue)
evalFBAE env expr = evalStatFAE env (elabFBAE expr)

-- FBAEC AST and Type Definitions

-- data FBAEC where
--  NumE :: Int -> FBAEC
--  PlusE :: FBAEC -> FBAEC -> FBAEC
--  MinusE :: FBAEC -> FBAEC -> FBAEC
--  TrueE :: FBAEC
--  FalseE :: FBAEC
--  AndE :: FBAEC -> FBAEC -> FBAEC
--  OrE :: FBAEC -> FBAEC -> FBAEC
--  NotE :: FBAEC -> FBAEC
--  IfE :: FBAEC -> FBAEC -> FBAEC -> FBAEC
--  LambdaE :: String -> FBAEC -> FBAEC
--  AppE :: FBAEC -> FBAEC -> FBAEC
--  BindE :: String -> FBAEC -> FBAEC -> FBAEC
--  IdE :: String -> FBAEC
--  deriving (Show,Eq)

-- elabFBAEC :: FBAEC -> FAE
-- elabFBAEC _ = (Num (-1))

-- evalFBAEC :: Env' -> FBAEC -> Maybe FAEValue
-- evalFBAEC _ _ = Nothing


-- -- Test cases for evalDynFAE
-- evalDynFAETestCases :: [(String, FAE, Maybe FAE)]
-- evalDynFAETestCases =
--   [ ("Test 1", Num 42, Just (Num 42))
--   , ("Test 2", Plus (Num 2) (Num 3), Just (Num 5))
--   , ("Test 3", Minus (Num 5) (Num 3), Just (Num 2))
--   , ("Test 4", Lambda "x" (Plus (Id "x") (Num 1)), Just (Lambda "x" (Plus (Id "x") (Num 1))))
--   , ("Test 5", App (Lambda "x" (Plus (Id "x") (Num 1))) (Num 10), Just (Num 11))
--   , ("Test 6", Id "x", Nothing)
--   , ("Test 7", App (Lambda "x" (Plus (Id "x") (Num 1))) (Num 10), Just (Num 11))
--   ]

-- -- Test cases for evalStatFAE
-- evalStatFAETestCases :: [(String, FAE, Maybe FAEValue)]
-- evalStatFAETestCases =
--   [ ("Test 1", Num 42, Just (NumV 42))
--   , ("Test 2", Plus (Num 2) (Num 3), Just (NumV 5))
--   , ("Test 3", Minus (Num 5) (Num 3), Just (NumV 2))
--   , ("Test 4", Lambda "x" (Plus (Id "x") (Num 1)), Just (ClosureV "x" (Plus (Id "x") (Num 1)) []))
--   , ("Test 5", App (Lambda "x" (Plus (Id "x") (Num 1))) (Num 10), Just (NumV 11))
--   , ("Test 6", Id "x", Nothing)
--   , ("Test 7", App (Lambda "x" (Plus (Id "x") (Num 1))) (Num 10), Just (NumV 11))
--   ]

-- -- Test cases for elabFBAE
-- elabFBAETestCases :: [(String, FBAE, FAE)]
-- elabFBAETestCases =
--   [ ("Test 1", NumD 42, Num 42)
--   , ("Test 2", PlusD (NumD 2) (NumD 3), Plus (Num 2) (Num 3))
--   , ("Test 3", MinusD (NumD 5) (NumD 3), Minus (Num 5) (Num 3))
--   , ("Test 4", LambdaD "x" (PlusD (IdD "x") (NumD 1)), Lambda "x" (Plus (Id "x") (Num 1)))
--   , ("Test 5", AppD (LambdaD "x" (PlusD (IdD "x") (NumD 1))) (NumD 10), App (Lambda "x" (Plus (Id "x") (Num 1))) (Num 10))
--   , ("Test 6", BindD "x" (NumD 10) (PlusD (IdD "x") (NumD 5)), App (Lambda "x" (Plus (Id "x") (Num 5))) (Num 10))
--   , ("Test 6", IdD "x", Id "x")
--   , ("Test 7", AppD (LambdaD "x" (PlusD (IdD "x") (NumD 1))) (NumD 10), App (Lambda "x" (Plus (Id "x") (Num 1))) (Num 10))
--   , ("Test 8", BindD "x" (NumD 10) (PlusD (IdD "x") (NumD 5)), App (Lambda "x" (Plus (Id "x") (Num 5))) (Num 10))
--   ]


-- main :: IO ()
-- main = do
--   putStrLn "\n Running evalDynFAE test cases:"
--   mapM_ runEvalDynFAETest evalDynFAETestCases

--   putStrLn "\n Running evalStatFAE test cases:"
--   mapM_ runEvalStatFAETest evalStatFAETestCases

--   putStrLn "\n Running elabFBAE test cases:"
--   mapM_ runElabFBAETest elabFBAETestCases

--   where
--     runEvalDynFAETest (name, input, expected) = do
--       let result = evalDynFAE [] input
--       putStrLn $ name ++ " (evalDynFAE): " ++ show result
--       if result == expected
--         then putStrLn "  Passed"
--         else putStrLn "  Failed"

--     runEvalStatFAETest (name, input, expected) = do
--       let result = evalStatFAE [] input
--       putStrLn $ name ++ " (evalStatFAE): " ++ show result
--       if result == expected
--         then putStrLn "  Passed"
--         else putStrLn "  Failed"

--     runElabFBAETest (name, input, expected) = do
--       let result = elabFBAE input
--       putStrLn $ name ++ " (elabFBAE): " ++ show result
--       if result == expected
--         then putStrLn "  Passed"
--         else putStrLn "  Failed"
