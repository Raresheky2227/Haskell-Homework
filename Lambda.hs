module Lambda where

import Expr
import Data.List

-- TODO 1.1. find free variables of a Expr
free_vars :: Expr -> [String]
free_vars expr = case expr of
  Variable x -> [x]
  Function param body -> filter (/= param) (free_vars body)
  Application e1 e2 -> free_vars e1 `union` free_vars e2
  where
    union :: [String] -> [String] -> [String]
    union xs ys = xs ++ filter (`notElem` xs) ys

-- TODO 1.2. reduce a redex
reduce :: Expr -> String -> Expr -> Expr
reduce expr param arg = case expr of
  Variable x -> if x == param then arg else Variable x
  Function p body ->
    let boundVars = free_vars body `union` [p]
        freshVar = findFreshVar boundVars
        body' = renameVar body p freshVar
    in Function freshVar (reduce body' param arg)
  Application e1 e2 -> Application (reduce e1 param arg) (reduce e2 param arg)



-- Normal Evaluation
-- TODO 1.3. perform one step of Normal Evaluation
stepN :: Expr -> Expr
stepN (Application (Function p body) arg) = replaceVar body p arg
stepN (Application e1 e2) =
  if isValue e1
    then Application e1 (stepN e2)
    else Application (stepN e1) e2
stepN (Function p body) = Function p (stepN body)  -- Recursively reduce the body of lambda abstraction
stepN expr@(Variable _) = expr  -- No reduction possible for variables

isValue :: Expr -> Bool
isValue (Function _ _) = True
isValue _ = False

replaceVar :: Expr -> String -> Expr -> Expr
replaceVar (Variable x) oldVar newVar = if x == oldVar then newVar else Variable x
replaceVar (Function p body) oldVar newVar = Function p (replaceVar body oldVar newVar)
replaceVar (Application e1 e2) oldVar newVar = Application (replaceVar e1 oldVar newVar) (replaceVar e2 oldVar newVar)


-- TODO 1.4. perform Normal Evaluation
reduceN :: Expr -> Expr
reduceN expr = head (reverse (reduceAllN expr))

reduceAllN :: Expr -> [Expr]
reduceAllN expr = expr : case reduceStep expr of
  Just reducedExpr -> reduceAllN reducedExpr
  Nothing -> []

reduceStep :: Expr -> Maybe Expr
reduceStep (Application (Function var body) arg) = Just (substitute body var arg)
reduceStep (Application func arg) = case reduceStep func of
  Just reducedFunc -> Just (Application reducedFunc arg)
  Nothing -> case reduceStep arg of
    Just reducedArg -> Just (Application func reducedArg)
    Nothing -> Nothing
reduceStep (Function var body) = case reduceStep body of
  Just reducedBody -> Just (Function var reducedBody)
  Nothing -> Nothing
reduceStep _ = Nothing

substitute :: Expr -> String -> Expr -> Expr
substitute (Variable y) x e
  | y == x = e
  | otherwise = Variable y
substitute (Function y e1) x e2
  | y == x = Function y e1
  | x `elem` freeVars e1 = let freshVar = findFreshVar (freeVars e1 `union` freeVars e2)
                          in Function freshVar (substitute (renameVar e1 y freshVar) x e2)
  | otherwise = Function y (substitute e1 x e2)
substitute (Application e1 e2) x e =
  Application (substitute e1 x e) (substitute e2 x e)

findFreshVar :: [String] -> String
findFreshVar boundVars = head (filter (`notElem` boundVars) freshVars)
  where
    freshVars = [c : show n | n <- [1..], c <- ['a'..'z']]

renameVar :: Expr -> String -> String -> Expr
renameVar (Variable x) oldVar newVar = if x == oldVar then Variable newVar else Variable x
renameVar (Function p body) oldVar newVar =
  let p' = if p == oldVar then newVar else p
  in Function p' (renameVar body oldVar newVar)
renameVar (Application e1 e2) oldVar newVar =
  Application (renameVar e1 oldVar newVar) (renameVar e2 oldVar newVar)


freeVars :: Expr -> [String]
freeVars (Variable x) = [x]
freeVars (Function p body) = freeVars body `without` p
freeVars (Application e1 e2) = freeVars e1 `union` freeVars e2

without :: [String] -> String -> [String]
without xs x = filter (/= x) xs


-- Applicative Evaluation
-- TODO 1.5. perform one step of Applicative Evaluation
isReducible :: Expr -> Bool
isReducible (Application (Function _ _) _) = True  -- Beta reduction is possible
isReducible (Application func arg) = isReducible func || isReducible arg  -- Recursively check reducibility of function and argument
isReducible _ = False  -- Default case: no further reduction is possible


betaReduction :: Expr -> Expr -> Expr
betaReduction (Function param body) arg = substitute param arg body
  where
    substitute :: String -> Expr -> Expr -> Expr
    substitute param arg (Variable x) | x == param = arg
    substitute param arg (Variable x) = Variable x
    substitute param arg (Function p b) = Function p (substitute param arg b)
    substitute param arg (Application e1 e2) = Application (substitute param arg e1) (substitute param arg e2)

-- Applicative evaluation step function
stepA :: Expr -> Expr
stepA (Application (Function param body) arg)
  | isReducible arg = Application (Function param body) (stepA arg)  -- Evaluate the argument first
  | otherwise = betaReduction (Function param body) arg  -- Perform beta reduction
stepA (Application func arg) = Application (stepA func) arg  -- Evaluate the function first
stepA expr = expr  -- No reduction possible, return the expression as is

-- TODO 1.6. perform Applicative Evaluation
reduceA :: Expr -> Expr
reduceA expr = head (reverse (reduceAllN expr))

reduceAllA :: Expr -> [Expr]
reduceAllA expr = expr : case stepA expr of
  nextExpr | nextExpr /= expr -> reduceAllA nextExpr
  _ -> []

-- TODO 3.1. make substitutions into a expression with Macros
evalMacros :: [(String, Expr)] -> Expr -> Expr
evalMacros _ expr@(Variable _) = expr
evalMacros macros (Function param body) = Function param (evalMacros macros body)
evalMacros macros (Application e1 e2) = Application (evalMacros macros e1) (evalMacros macros e2)
evalMacros macros (Macro name) = case lookup name macros of
  Just expr -> evalMacros macros expr
  Nothing -> Macro name

-- TODO 4.1. evaluate code sequence using given strategy
evalCode :: (Expr -> Expr) -> [Code] -> [Expr]
evalCode strategy codes = evalCode1 strategy codes

replace :: [Expr] -> Expr -> Expr -> [Expr]
replace exprs targetExpr replacementExpr =
  case reverse exprs of
    (lastExpr:revInitExprs) ->
      if lastExpr == targetExpr
        then reverse (replacementExpr:revInitExprs)
        else exprs
    _ -> exprs

evalCode1 :: (Expr -> Expr) -> [Code] -> [Expr]
evalCode1 strategy codes = eval [] codes
  where
    eval _ [] = []  -- No more codes, return empty list
    eval env (Evaluate expr : rest) =
      let evaluatedExpr = evalMacros1 env expr  -- Evaluate macros in the expression using evalMacros1
          result = strategy (substitute env evaluatedExpr)  -- Evaluate the expression using the strategy
      in result : eval env rest  -- Collect the result and process the remaining codes
    eval env (Assign var expr : rest) =
      let evaluatedExpr = evalMacros1 env expr  -- Evaluate macros in the expression using evalMacros1
          result = strategy (substitute env evaluatedExpr)  -- Evaluate the expression using the strategy
          updatedEnv = (var, result) : env  -- Update the environment with the evaluated expression
      in eval updatedEnv rest  -- Process the remaining codes with the updated environment

    evalMacros1 :: [(String, Expr)] -> Expr -> Expr
    evalMacros1 env (Macro name) =
      case lookup name env of
      Just expr -> evalMacros1 env expr  -- Evaluate the macro recursively
      Nothing -> Macro name  -- Macro not found in the environment, leave it unchanged
    evalMacros1 env (Function name expr) = Function name (evalMacros1 env expr)  -- Evaluate the macro in the function body
    evalMacros1 env (Application e1 e2) = Application (evalMacros1 env e1) (evalMacros1 env e2)  -- Evaluate macros in the application
    evalMacros1 _ expr = expr  -- For variables, return as is

    substitute :: [(String, Expr)] -> Expr -> Expr
    substitute [] expr = expr
    substitute ((var, expr') : rest) expr = substitute rest (substituteSingle var expr' expr)

    substituteSingle :: String -> Expr -> Expr -> Expr
    substituteSingle var expr' (Variable y) | y == var = expr'
                                            | otherwise = Variable y
    substituteSingle var expr' (Function y e1) | y == var = Function y e1
                                               | otherwise = Function y (substituteSingle var expr' e1)
    substituteSingle var expr' (Application e1 e2) = Application (substituteSingle var expr' e1) (substituteSingle var expr' e2)
    substituteSingle _ _ expr = expr

