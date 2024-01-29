{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Eta reduce" #-}

import qualified System.Exit as Exit
import Test.HUnit

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
  -- Sum rules
  Sum (Num 0) a -> simpl a
  Sum a (Num 0) -> simpl a
  Sum a b | a == b -> Prod (Num 2) (simpl a)
  Sum (Num a) (Num b) -> Num (a + b)
  Sum a b -> Sum (simpl a) (simpl b)
  -- Product rules
  Prod (Num 0) _ -> Num 0
  Prod _ (Num 0) -> Num 0
  Prod (Num 1) a -> simpl a
  Prod a (Num 1) -> simpl a
  Prod (Num a) (Num b) -> Num (a * b)
  Prod a b | a == b -> Pow (simpl a) (Num 2)
  Prod a b -> Prod (simpl a) (simpl b)
  -- Power rules
  Pow _ (Num 0) -> Num 1 -- x^0 = 1 (for x > 0)
  Pow a (Num 1) -> simpl a -- x^1 = x
  Pow (Num 1) _ -> Num 1 -- 1^x = 1
  Pow base (Num n)
    | n == 0 -> Num 1 -- x^0 = 1
    | n == 1 -> simpl base -- x^1 = x
  Pow (Num 0) _ -> Num 0 -- TODO: 0^x = 0 (for x > 0)
  Pow (Num a) (Num b) -> Num (a ** b) -- (a^b) = a^b
  Pow base expo -> Pow (simpl base) (simpl expo) -- Simplify base and exponent recursively
  -- Negation rules
  Neg (Num x) -> Num (-x) -- Simplify negation of a numeric constant
  Neg (Neg a) -> simpl a -- Double negation simplification
  Neg (Sum a b) -> Sum (simpl (Neg a)) (simpl (Neg b)) -- Distribute negation over sum
  Neg (Prod a b) -> Prod (simpl (Neg a)) (simpl (Neg b)) -- Distribute negation over product
  Neg (Pow a b) -> Pow (simpl (Neg a)) (simpl b) -- Distribute negation over base of power
  Neg (Inv a) -> Inv (simpl (Neg a)) -- Distribute negation over inversion
  Neg v -> Neg (simpl v)
  _ -> expr

testSimplRep :: Test
testSimplRep =
  TestList
    [ TestCase $ do
        let expected = Num 42
        let actual = simplRep (Num 42)
        assertEqual "Simplification of a numeric constant" expected actual,
      TestCase $ do
        let expected = Num 5
        let actual = simplRep (Sum (Num 5) (Num 0))
        assertEqual "Simplification involving zero" expected actual,
      TestCase $ do
        let expected = Prod (Num 3) (Pow (Var "x") (Num 2))
        let actual = simplRep (Prod (Prod (Num 1) (Num 3)) (Pow (Var "x") (Num 2)))
        assertEqual "Simplification involving multiplication and power" expected actual,
      TestCase $ do
        let expected = Num 2
        let actual = simplRep (Sum (Num 1) (Neg (Neg (Neg (Neg (Num 1))))))
        assertEqual "Simplification involving multiple negations" expected actual,
      TestCase $ do
        let expected = Pow (Sum (Var "x") (Num 4)) (Num 2)
        let actual = simplRep (Pow (Sum (Var "x") (Sum (Num 1) (Num 3))) (Prod (Num 2) (Sum (Num 0) (Num 1))))
        assertEqual "Simplification involving powers" expected actual
    ]

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

-- | Evaluates a Taylor series for the given expression, variable, center, and deg.
series :: Expr -> String -> Double -> Int -> Expr
series expr var center deg = sumTerms 0
  where
    -- Calculates the n-th factorial.
    fact :: Double -> Double
    fact 0 = 1
    fact n = n * fact (n - 1)

    sumTerms :: Int -> Expr
    sumTerms n
      | n > deg = Num 0
      | otherwise = Sum (term n) (sumTerms (n + 1))

    term :: Int -> Expr
    term n =
      let coef = Num (1 / fact (fromIntegral n))
          offset = sub (Var var) (Num center)
          powerTerm = Pow offset (Num (fromIntegral n))
          nthDeriv = repl (derivN n var expr) (Var var) (Num center)
       in Prod (Prod nthDeriv coef) powerTerm

-- | Test cases for the 'simpl' function.
testSeries :: Test
testSeries =
  TestList
    [ TestCase $ do
        let expected = Sum (Num (-2)) (Sum (Prod (Num (-2)) (Sum (Var "x") (Num (-1)))) (Pow (Sum (Var "x") (Num (-1))) (Num 2)))
        let actual = series (Sum (Pow (Var "x") (Num 2)) (Sum (Prod (Num (-4)) (Var "x")) (Num 1))) "x" 1 2
        assertEqual "Taylor series expansion of x^2 - 4x + 1 at center x = 1, degree = 2" expected (simplRep actual)
    ]

main :: IO ()
main = do
  result <-
    runTestTT
      ( TestList
          [ TestLabel "Taylor series tests" testSeries,
            TestLabel "Simplification tests" testSimplRep
          ]
      )
  if failures result > 0 then Exit.exitFailure else Exit.exitSuccess