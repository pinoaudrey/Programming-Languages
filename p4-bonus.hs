{-# LANGUAGE GADTs #-}

-- import Control.Monad

-- Calculator language extended with an environment to hold defined variables

data TFBAE where
  TNum :: TFBAE
  TBool :: TFBAE
  TLoc :: TFBAE -> TFBAE
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
  New :: FBAE -> FBAE
  Set :: FBAE -> FBAE -> FBAE
  Deref :: FBAE -> FBAE
  Seq :: FBAE -> FBAE -> FBAE
  Loc :: Int -> FBAE  
  deriving (Show,Eq)


-- Value defintion for statically scoped eval

data FBAEVal where
  NumV :: Int -> FBAEVal
  BooleanV :: Bool -> FBAEVal
  ClosureV :: String -> FBAE -> Env -> FBAEVal
  LocV :: Int -> FBAEVal
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
subst i v (New e) = New (subst i v e)
subst i v (Set l e) = Set (subst i v l) (subst i v e)
subst i v (Deref e) = Deref (subst i v e)
subst i v (Seq e1 e2) = Seq (subst i v e1) (subst i v e2)
subst i v (Loc l) = Loc l

type Loc = Int
type Sto = Loc -> Maybe FBAEVal
type Store = (Loc, Sto)

initSto :: Sto
initSto x = Nothing

setSto :: Sto -> Loc -> FBAEVal -> Sto
setSto s l v = \m -> if m == l then Just v else s m

initStore :: Store
initStore = (0, initSto)

derefStore :: Store -> Loc -> Maybe FBAEVal
derefStore (_, s) l = s l

setStore :: Store -> Loc -> FBAEVal -> Store
setStore (i, s) l v = (i, setSto s l v)

newStore :: Store -> Store
newStore (i, s) = (i + 1, \m -> if m == i then Nothing else s m)

evalM :: Env -> Store -> FBAE -> Maybe (Store,FBAEVal)
evalM env sto (Num x) = return (sto,(NumV x))
evalM env sto (Plus l r) = do { (sto',(NumV l')) <- (evalM env sto l) ;
                                (sto'',(NumV r')) <- (evalM env sto' r) ;
                                return (sto'',(NumV (l'+r'))) }
evalM env sto (Minus l r) = do { (sto',(NumV l')) <- (evalM env sto l) ;
                                 (sto'',(NumV r')) <- (evalM env sto' r) ;
                                 return (sto'',(NumV (l'-r'))) }
evalM env sto (Mult l r) = do { (sto',(NumV l')) <- (evalM env sto l) ;
                                (sto'',(NumV r')) <- (evalM env sto' r) ;
                                return (sto'',(NumV (l'*r'))) }
evalM env sto (Div l r) = do { (sto', NumV l') <- evalM env sto l ;
                               (sto'', NumV r') <- evalM env sto' r ;
                               if r' == 0
                               then Nothing
                               else return (sto'', NumV (div l' r')) }
evalM env sto (Bind i v b) = do { (sto',v') <- (evalM env sto v) ;
                                 evalM ((i,v'):env) sto' b }
evalM env sto (Lambda i t b) = return (sto,(ClosureV i b env))
evalM env sto (App f a) = do { (sto',(ClosureV i b e)) <- (evalM env sto f) ;
                              (sto'',a') <- (evalM env sto' a) ;
                              (evalM ((i,a'):e) sto'' b) }
evalM env sto (Id i) = case lookup i env of
                        Just v -> Just (sto, v)
                        Nothing -> Nothing
evalM env sto (Boolean b) = return (sto,(BooleanV b))
evalM env sto (And l r) = do { (sto',(BooleanV l')) <- (evalM env sto l) ;
                               (sto'',(BooleanV r')) <- (evalM env sto' r) ;
                               return (sto'',(BooleanV (l'&&r'))) }
evalM env sto (Or l r) = do { (sto',(BooleanV l')) <- (evalM env sto l) ;
                              (sto'',(BooleanV r')) <- (evalM env sto' r) ;
                              return (sto'',(BooleanV (l'||r'))) }
evalM env sto (Leq l r) = do { (sto',(NumV l')) <- (evalM env sto l) ;
                               (sto'',(NumV r')) <- (evalM env sto' r) ;
                               return (sto'',(BooleanV (l'<=r'))) }
evalM env sto (IsZero t) = do { (sto',(NumV t')) <- (evalM env sto t) ;
                                return (sto',(BooleanV (t'==0))) }
evalM env sto (If c t e) = do { (sto',(BooleanV c')) <- (evalM env sto c) ;
                               (if c'
                                then (evalM env sto' t)
                                else (evalM env sto' e)) }
evalM env sto (New t) = do { (sto', v') <- evalM env sto t ;
                             let newSto = newStore sto' in
                             let (newLoc, _) = newSto in
                             return (setStore newSto newLoc v', LocV newLoc) }
evalM env sto (Set l t) = do { (sto', LocV loc) <- evalM env sto l ;
                               (sto'', v') <- evalM env sto' t ;
                               return (setStore sto'' loc v', v') }

evalM env sto (Deref t) = do { (sto', LocV loc) <- evalM env sto t ;
                               case derefStore sto' loc of
                                 Just v -> Just (sto', v)
                                 Nothing -> Nothing }

evalM env sto (Seq l r) = do { (sto', _) <- evalM env sto l ;
                               evalM env sto' r }

evalM env sto (Fix f) = do { (sto', ClosureV i b e) <- evalM env sto f ;
                             evalM env sto' (subst i (Fix (Lambda i TNum b)) b) }


type Cont = [(String,TFBAE)]

typeofM :: Cont -> FBAE -> (Maybe TFBAE)
typeofM cont (Num x) = return TNum
typeofM cont (Boolean b) = return TBool
typeofM cont (Plus l r) = do { TNum <- (typeofM cont l) ;
                               TNum <- (typeofM cont r) ;
                               return TNum }
typeofM cont (Minus l r) = do { TNum <- (typeofM cont l) ;
                                TNum <- (typeofM cont r) ;
                                return TNum }
typeofM cont (Mult l r) = do { TNum <- (typeofM cont l) ;
                               TNum <- (typeofM cont r) ;
                               return TNum }
typeofM cont (Div l r) = do { TNum <- (typeofM cont l) ;
                              TNum <- (typeofM cont r) ;
                              return TNum }
typeofM cont (Bind i v b) = do { v' <- typeofM cont v ;
                                 typeofM ((i,v'):cont) b }
typeofM cont (Id id) = (lookup id cont)
typeofM cont (Lambda x t b) = do { tyB <- typeofM ((x,t):cont) b ;
                                   return (t :->: tyB) }
typeofM cont (App x y) = do { tyXd :->: tyXr <- typeofM cont x ;
                              tyY <- typeofM cont y ;
                              if tyXd==tyY
                              then return tyXr
                              else Nothing }
typeofM cont (Fix f) = do { (tyXd :->: tyXr) <- (typeofM cont f) ;
                            return tyXr }

typeofM cont (And l r) = do { TBool <- (typeofM cont l) ;
                              TBool <- (typeofM cont r) ;
                              return TBool }
typeofM cont (Or l r) = do { TBool <- (typeofM cont l) ;
                             TBool <- (typeofM cont r);
                             return TBool }
typeofM cont (Leq l r) = do { TNum <- (typeofM cont l) ;
                              TNum <- (typeofM cont r) ;
                              return TBool }
typeofM cont (IsZero v) = do { TNum <- (typeofM cont v) ;
                               return TBool }
typeofM cont (If c t e) = do { TBool <- (typeofM cont c) ;
                               t' <- (typeofM cont t) ;
                               e' <- (typeofM cont e) ;
                               if t' == e'
                               then return t'
                               else Nothing }
typeofM cont (New t) = do { t' <- (typeofM cont t) ;
                            return (TLoc t') }
typeofM cont (Set l v) = do { (TLoc l') <- (typeofM cont l) ;
                              v' <- (typeofM cont v) ;
                              if l'==v'
                              then return v'
                              else Nothing }
typeofM cont (Deref l) = do { (TLoc l') <- (typeofM cont l) ;
                              return l'}
typeofM cont (Seq l r) = do { (typeofM cont l) ;
                              (typeofM cont r) }


-- Interpreter

interp :: FBAE -> Maybe FBAEVal
interp f = do
  let env = []
  let sto = initStore
  (_, val) <- evalM env sto f
  return val


-- ***************** Test Cases *****************
-- **********************************************


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
test6 :: FBAE
test6 = Bind "x" 
    (New (Num 10)) 
    (Bind "f" 
      (Fix (Lambda "f" (TNum :->: TNum) 
        (Lambda "y" TNum 
          (If (Leq (Id "y") (Num 0))
              (Deref (Id "x"))
              (Seq (Set (Id "x") (Plus (Deref (Id "x")) (Num 1)))
                   (App (Id "f") (Minus (Id "y") (Num 1))))))))
      (App (Id "f") (Num 3)))

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

test11 :: FBAE
test11 = Bind "x" (Num 5) (Plus (Id "x") (Num 3))

test12 :: FBAE
test12 = Bind "x" (New (Num 10)) (Deref (Id "x"))

test13 :: FBAE
test13 = Bind "x" (New (Num 10)) (Seq (Set (Id "x") (Num 20)) (Deref (Id "x")))

test14 :: FBAE
test14 = App (Fix (Lambda "f" (TNum :->: TNum) 
                             (Lambda "x" TNum 
                               (If (IsZero (Id "x")) 
                                   (Num 0) 
                                   (App (Id "f") (Minus (Id "x") (Num 1))))))) 
                          (Num 5)

test15 :: FBAE
test15 = Bind "x" 
    (New (Num 10)) 
    (Bind "f" 
      (Fix (Lambda "f" (TNum :->: TNum) 
        (Lambda "y" TNum 
          (If (IsZero (Id "y")) 
              (Deref (Id "x")) 
              (Seq (Set (Id "x") (Plus (Deref (Id "x")) (Num 1))) 
                   (App (Id "f") (Minus (Id "y") (Num 1))))))))
      (App (Id "f") (Num 2)))


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

    putStrLn "\nTest Case 6:"
    printResult "test6" (interp test6)

    putStrLn "\nTest Case 7:"
    printResult "test7" (interp test7)

    putStrLn "\nTest Case 8:"
    printResult "test8" (interp test8)

    putStrLn "\nTest Case 9:"
    printResult "test9" (interp test9)

    putStrLn "\nTest Case 10:"
    printResult "test10" (interp test10)

    putStrLn "\nTest Case 11:"
    printResult "test11" (interp test11)

    putStrLn "\nTest Case 12:"
    printResult "test12" (interp test12)

    putStrLn "\nTest Case 13:"
    printResult "test13" (interp test13)

    putStrLn "\nTest Case 14:"
    printResult "test14" (interp test14)

    putStrLn "\nTest Case 15:"
    printResult "test15" (interp test15)

-- Helper function to print results
printResult :: String -> Maybe FBAEVal -> IO ()
printResult testName result =
    case result of
        Just val -> putStrLn $ testName ++ " Result: " ++ show val
        Nothing  -> putStrLn $ testName ++ " Error during evaluation or type inference"