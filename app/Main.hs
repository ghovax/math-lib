{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Eta reduce" #-}

-- |
-- Module      : Main
-- Description : Provides operations for manipulating the Expr data type.
--
-- This module defines various operations on the 'Expr' data type, including substitution, simplification, and repeated simplification.
data Expr
  = -- | Addition operation
    Sum Expr Expr
  | -- | Numeric constant
    Num Double
  | -- | Negation operation
    Neg Expr
  | -- | Multiplication operation
    Prod Expr Expr
  | -- | Variable
    Var String
  | -- | Exponentiation operation
    Pow Expr Expr
  | -- | Inversion operation
    Inv Expr
  deriving (Show, Eq)

-- | Subtracts expression 'b' from 'a'.
sub :: Expr -> Expr -> Expr
sub a b = Sum a (Neg b)

-- | Left division: Divides expression 'a' by 'b'.
ldiv :: Expr -> Expr -> Expr
ldiv a b = Prod a (Inv b)

-- | Right division: Divides expression 'b' by 'a'.
rdiv :: Expr -> Expr -> Expr
rdiv a b = Prod (Inv a) b

-- | Replaces occurrences of 'targ' with 'rule' in the expression.
repl :: Expr -> Expr -> Expr -> Expr
repl (Sum a b) targ rule = Sum (repl a targ rule) (repl b targ rule)
repl (Num x) _ _ = Num x
repl (Neg a) targ rule = Neg (repl a targ rule)
repl (Prod a b) targ rule = Prod (repl a targ rule) (repl b targ rule)
repl (Var v) targ rule
  | Var v == targ = rule
  | otherwise = Var v
repl (Pow a b) targ rule = Pow (repl a targ rule) (repl b targ rule)
repl (Inv a) targ rule = Inv (repl a targ rule)

-- | Replaces all occurrences of target expressions with their corresponding rules.
replAll :: Expr -> [(Expr, Expr)] -> Expr
replAll e s = foldl (\a (targ, rule) -> repl a targ rule) e s

-- | Simplifies the expression by evaluating constant subexpressions.
simpl :: Expr -> Expr
simpl expr = case expr of
  Sum (Num a) (Num b) -> Num (a + b)
  Neg (Num a) -> Num (-a)
  Prod (Num a) (Num b) -> Num (a * b)
  Sum a b -> Sum (simpl a) (simpl b)
  Neg a -> Neg (simpl a)
  Prod a b -> Prod (simpl a) (simpl b)
  _ -> expr

-- | Repeatedly applies 'simpl' until the expression no longer changes.
simplRep :: Expr -> Expr
simplRep expr = let s = simpl expr in if s == expr then s else simplRep s

-- | Calculates the derivative of the expression with respect to the given variable.
deriv :: String -> Expr -> Expr
deriv var expr = case expr of
  Var v
    | v == var -> Num 1 -- Derivative of the variable with respect to itself is 1
    | otherwise -> Num 0 -- Derivative of a constant with respect to any variable is 0
  Num _ -> Num 0 -- Derivative of a constant with respect to any variable is 0
  Sum a b -> Sum (deriv var a) (deriv var b)
  Neg a -> Neg (deriv var a)
  Prod a b ->
    Sum (Prod (deriv var a) b) (Prod a (deriv var b))
  Pow base expo ->
    Prod expo (Prod (Pow base (sub expo (Num 1))) (deriv var base))
  Inv a -> Neg (ldiv (deriv var a) (Pow a (Num 2)))

-- | Calculates the n-th derivative of the expression with respect to the given variable.
derivN :: Int -> String -> Expr -> Expr
derivN 0 _ expr = expr
derivN n var expr = derivN (n - 1) var (deriv var expr)

main :: IO ()
main = do
  -- Example usage of 'repl'
  let expr = Sum (Var "x") (Prod (Num 3) (Neg (Var "y")))
  let subs = [(Var "x", Num 5), (Var "y", Num 2)]
  print (simplRep (replAll expr subs))