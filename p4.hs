{-# LANGUAGE GADTs #-}

-- import Control.Monad

-- Calculator language extended with an environment to hold defined variables

data TFBAE where
  TNum :: TFBAE
  TBool :: TFBAE
  (:->:) :: TFBAE -> TFBAE -> TFBAE
  deriving (Show,Eq)

data FBAE where
  Num :: Int -> FBAE
  Plus :: FBAE -> FBAE -> FBAE
  Minus :: FBAE -> FBAE -> FBAE
  Mult :: FBAE -> FBAE -> FBAE
  Div :: FBAE -> FBAE -> FBAE
  Bind :: String -> FBAE -> FBAE -> FBAE
  Lambda :: String -> TFBAE -> FBAE -> FBAE
  App :: FBAE -> FBAE -> FBAE
  Id :: String -> FBAE
  Boolean :: Bool -> FBAE
  And :: FBAE -> FBAE -> FBAE
  Or :: FBAE -> FBAE -> FBAE
  Leq :: FBAE -> FBAE -> FBAE
  IsZero :: FBAE -> FBAE
  If :: FBAE -> FBAE -> FBAE -> FBAE
  Fix :: FBAE -> FBAE
  deriving (Show,Eq)

-- Value defintion for statically scoped eval

data FBAEVal where
  NumV :: Int -> FBAEVal
  BooleanV :: Bool -> FBAEVal
  -- ClosureV :: String -> TFBAE -> FBAE -> Env -> FBAEVal
  ClosureV :: String -> FBAE -> Env -> FBAEVal
  deriving (Show,Eq)

-- Enviornment for statically scoped eval

type Env = [(String,FBAEVal)]

subst :: String -> FBAE -> FBAE -> FBAE
subst _ _ (Num x) = (Num x)
subst i v (Plus l r) = (Plus (subst i v l) (subst i v r))
subst i v (Minus l r) = (Minus (subst i v l) (subst i v r))
subst i v (Mult l r) = (Mult (subst i v l) (subst i v r))
subst i v (Div l r) = (Div (subst i v l) (subst i v r))
subst i v (Bind i' v' b') = if i==i'
                            then (Bind i' (subst i v v') b')
                            else (Bind i' (subst i v v') (subst i v b'))
subst i v (Lambda i' ty b') = if i==i'
                             then (Lambda i' ty b')
                             else (Lambda i' ty (subst i v b'))
subst i v (App f a) = (App (subst i v f) (subst i v a))
subst i v (Id i') = if i==i'
                    then v
                    else (Id i')
subst i v (Boolean b) = (Boolean b)
subst i v (And l r) = (And (subst i v l) (subst i v r))
subst i v (Or l r) = (Or (subst i v l) (subst i v r))
subst i v (Leq l r) = (Leq (subst i v l) (subst i v r))
subst i v (IsZero t) = (IsZero (subst i v t))
subst i v (If c l r) = (If (subst i v c) (subst i v l) (subst i v r))
subst i v (Fix t) = (Fix (subst i v t))

-- Statically scoped eval
         
evalM :: Env -> FBAE -> (Maybe FBAEVal)
evalM env (Num x) = Just (NumV x)
evalM env (Boolean x) = Just (BooleanV x)
evalM env (Plus l r) = do {
  (NumV l') <- evalM env l;
  (NumV r') <- evalM env r;
  return (NumV (l' + r'))
}
evalM env (Minus l r) = do {
  (NumV l') <- evalM env l;
  (NumV r') <- evalM env r;
  if l' >= r' then return (NumV (l' - r')) else Nothing
}
evalM env (Mult l r) = do {
  (NumV l') <- evalM env l;
  (NumV r') <- evalM env r;
  return (NumV (l' * r'))
}
evalM env (Div l r) = do {
  (NumV l') <- evalM env l;
  (NumV r') <- evalM env r;
  if r' /= 0 then return (NumV (l' `div` r')) else Nothing
}
evalM env (Bind i v b) = do {
  v' <- evalM env v;
  evalM ((i,v'):env) b
}
evalM env (Lambda i t b) = Just (ClosureV i b env)
evalM env (App f a) = do {
  (ClosureV i b env') <- (evalM env f);
  a' <- (evalM env a);
  (evalM ((i,a'):env') b)
}
evalM env (Id i) = lookup i env
evalM env (And l r) = do {
  (BooleanV l') <- evalM env l;
  (BooleanV r') <- evalM env r;
  return (BooleanV (l' && r'))
}
evalM env (Or l r) = do {
  (BooleanV l') <- evalM env l;
  (BooleanV r') <- evalM env r;
  return (BooleanV (l' || r'))
}
evalM env (Leq l r) = do {
  (NumV l') <- evalM env l;
  (NumV r') <- evalM env r;
  return (BooleanV (l' <= r'))
}
evalM env (IsZero i) = do {
  (NumV i') <- evalM env i;
  return (BooleanV (i' == 0))
}
evalM env (If c t f) = do {
  (BooleanV c') <- evalM env c;
  if c' then evalM env t else evalM env f
}
evalM env (Fix f) = do {
  (ClosureV i b env') <- (evalM env f);
  t <- Just TNum;
  (evalM env' (subst i (Fix (Lambda i t b)) b))
}

-- Type inference function

type Cont = [(String,TFBAE)]

typeofM :: Cont -> FBAE -> (Maybe TFBAE)
typeofM _ (Num _) = Just TNum
typeofM _ (Boolean _) = Just TBool
typeofM c (Plus l r) = do { l' <- (typeofM c l);
                            r' <- (typeofM c r);
                            if l'==TNum && r'==TNum then return TNum else Nothing }
typeofM c (Minus l r) = do { l' <- (typeofM c l);
                             r' <- (typeofM c r);
                             if l'==TNum && r'==TNum then return TNum else Nothing }
typeofM c (Mult l r) = do { l' <- (typeofM c l);
                            r' <- (typeofM c r);
                            if l'==TNum && r'==TNum then return TNum else Nothing }
typeofM c (Div l r) = do { l' <- (typeofM c l);
                           r' <- (typeofM c r);
                           if l'==TNum && r'==TNum then return TNum else Nothing }
typeofM c (And l r) = do { l' <- (typeofM c l);
                            r' <- (typeofM c r);
                            if l'==TBool && r'==TBool then return TBool else Nothing }
typeofM c (Or l r) = do { l' <- (typeofM c l);
                            r' <- (typeofM c r);
                            if l'==TBool && r'==TBool then return TBool else Nothing }
typeofM c (Leq l r) = do { l' <- (typeofM c l);
                            r' <- (typeofM c r);
                            if l'==TNum && r'==TNum then return TBool else Nothing }
typeofM c (IsZero i) = do { i' <- (typeofM c i);
                            if i'==TNum then return TBool else Nothing }
typeofM c (If v t e) = do { v' <- (typeofM c v);
                            t' <- (typeofM c t);
                            e' <- (typeofM c e);
                            if v'==TBool && t'==e' then return t' else Nothing }
typeofM c (Bind i v b) = do { v' <- (typeofM c v);
                            (typeofM ((i,v'):c) b) }
typeofM c (Lambda i t b) = do { r <- (typeofM ((i,t):c) b);
                              return (t:->:r) }
typeofM c (App f a) = do { a' <- (typeofM c a);
                           (d:->:r) <- (typeofM c f);
                           if d==a' then return r else Nothing }
typeofM c (Id i) = lookup i c
typeofM c (Fix f) = do { (d:->:r) <- (typeofM c f);
                         return r }

-- Interpreter

interp :: FBAE -> (Maybe FBAEVal)
interp f = let env = [] in
           do { typeofM env f;
                evalM env f }

-- Factorial function for testing evalM and typeofM.  the type of test1 should
-- be TNum and the result of evaluating test1`should be (NumV 6).  Remember
-- that Just is used to return both the value and type.

-- test1 = (Bind "f" (Lambda "g" ((:->:) TNum TNum)
--                     (Lambda "x" TNum (If (IsZero (Id "x")) (Num 1)
--                                          (Mult (Id "x")
--                                                (App (Id "g")
--                                                     (Minus (Id "x")
--                                                            (Num 1)))))))
--          (App (Fix (Id "f")) (Num 3)))


-- Test Case 1: Simple arithmetic expression
test1 :: FBAE
test1 = Plus (Num 2) (Num 3)

-- Test Case 2: Variable binding and usage
test2 :: FBAE
test2 = Bind "x" (Num 5) (Plus (Id "x") (Num 2))

-- Test Case 3: Lambda function application
test3 :: FBAE
test3 = App (Lambda "x" TNum (Plus (Id "x") (Num 1))) (Num 3)

-- Test Case 4: If-else expression
test4 :: FBAE
test4 = If (IsZero (Num 0)) (Num 1) (Num 2)

-- Factorial function for testing evalM and typeofM.  the type of test1 should
-- be TNum and the result of evaluating test1`should be (NumV 6).  Remember
-- that Just is used to return both the value and type.

-- Test Case 5: Recursive factorial function
test5 :: FBAE
test5 = Bind "f" (Lambda "g" ((:->:) TNum TNum)
                    (Lambda "x" TNum (If (IsZero (Id "x")) (Num 1)
                                         (Mult (Id "x")
                                               (App (Id "g")
                                                    (Minus (Id "x") (Num 1)))))))
         (App (Fix (Id "f")) (Num 3))

--Test Case 6: New, Set, and Deref operations
-- test6 :: FBAE
-- test6 = Bind "x"
--     (New (Num 10))
--     (Bind "f"
--       (Lambda "y" TNum (Seq (Set (Id "x") (Plus (Deref (Id "x")) (Id "y")))
--                              (Deref (Id "x"))))
--       (App (Fix (Lambda "f" (TNum :->: TNum) (Lambda "x" TNum (App (Id "f") (Num 5)))))
--            (Num 3)))

-- Test Case 7: Logical operations
test7 :: FBAE
test7 = And (Boolean True) (Or (Boolean False) (Boolean True))

-- Test Case 8: Error case - Division by zero
test8 :: FBAE
test8 = Div (Num 5) (Num 0)

-- Test Case 9: Error case - Undefined variable
test9 :: FBAE
test9 = Id "undefinedVariable"

-- Test Case 10: Error case - Type mismatch in Lambda application
test10 :: FBAE
test10 = App (Lambda "x" TNum (Plus (Id "x") (Num 1))) (Boolean True)

main :: IO ()
main = do
    putStrLn "Test Case 1:"
    printResult "test1" (interp test1)

    putStrLn "\nTest Case 2:"
    printResult "test2" (interp test2)

    putStrLn "\nTest Case 3:"
    printResult "test3" (interp test3)

    putStrLn "\nTest Case 4:"
    printResult "test4" (interp test4)

    putStrLn "\nTest Case 5:"
    printResult "test5" (interp test5)

    -- putStrLn "\nTest Case 6:"
    -- printResult "test6" (interp test6)

    putStrLn "\nTest Case 7:"
    printResult "test7" (interp test7)

    putStrLn "\nTest Case 8:"
    printResult "test8" (interp test8)

    putStrLn "\nTest Case 9:"
    printResult "test9" (interp test9)

    putStrLn "\nTest Case 10:"
    printResult "test10" (interp test10)

-- Helper function to print results
printResult :: String -> Maybe FBAEVal -> IO ()
printResult testName result =
    case result of
        Just val -> putStrLn $ testName ++ " Result: " ++ show val
        Nothing  -> putStrLn $ testName ++ " Error during evaluation or type inference"