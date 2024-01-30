{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Eta reduce" #-}

import Data.List
import qualified System.Exit as Exit
import Test.HUnit

-- |
-- Module      : Main
-- Description : Provides operations for manipulating the Expr data type.

-- This module defines various operations on the 'Expr' data type, including substitution, simplification, and repeated simplification.
data Expr
  = Sum Expr Expr
  | Real Double
  | Neg Expr
  | Prod Expr Expr
  | Var String
  | Pow Expr Expr
  | Inv Expr
  | List [Expr]
  | Log Expr Expr
  | Ln Expr
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
repl expr targ rule = case expr of
  Sum a b -> Sum (repl a targ rule) (repl b targ rule)
  Neg a -> Neg (repl a targ rule)
  Prod a b -> Prod (repl a targ rule) (repl b targ rule)
  Var v -> case targ of
    Var tar | tar == v -> rule
    _ -> Var v
  Pow a b -> Pow (repl a targ rule) (repl b targ rule)
  Inv a -> Inv (repl a targ rule)
  List lst -> List (map (\e -> repl e targ rule) lst)
  Log base arg -> Log (repl base targ rule) (repl arg targ rule)
  Ln arg -> Ln (repl arg targ rule)
  _ -> expr

-- | Replaces all occurrences of target expressions with their corresponding rules.
replAll :: Expr -> [(Expr, Expr)] -> Expr
replAll e s = foldl (\a (targ, rule) -> repl a targ rule) e s

-- | Simplifies the expression by evaluating constant subexpressions.
simpl :: Expr -> Expr
simpl expr = case expr of
  -- Sum rules
  Sum (Real 0) a -> simpl a
  Sum a (Real 0) -> simpl a
  Sum a b | a == b -> Prod (Real 2) (simpl a)
  Sum (Real a) (Real b) -> Real (a + b)
  Sum a b -> Sum (simpl a) (simpl b)
  -- Product rules
  Prod (Real 0) _ -> Real 0
  Prod _ (Real 0) -> Real 0
  Prod (Real 1) a -> simpl a
  Prod a (Real 1) -> simpl a
  Prod (Real a) (Real b) -> Real (a * b)
  Prod a b | a == b -> Pow (simpl a) (Real 2)
  Prod a b -> Prod (simpl a) (simpl b)
  -- Power rules
  Pow _ (Real 0) -> Real 1 -- x^0 = 1 (for x > 0)
  Pow a (Real 1) -> simpl a -- x^1 = x
  Pow (Real 1) _ -> Real 1 -- 1^x = 1
  Pow base (Real n)
    | n == 0 -> Real 1 -- x^0 = 1
    | n == 1 -> simpl base -- x^1 = x
  Pow (Real 0) _ -> Real 0 -- TODO: 0^x = 0 (for x > 0)
  Pow (Real a) (Real b) -> Real (a ** b) -- (a^b) = a^b
  Pow base expo -> Pow (simpl base) (simpl expo) -- Simplify base and exponent recursively
  -- Negation rules
  Neg (Real x) -> Real (-x) -- Simplify negation of a numeric constant
  Neg (Neg a) -> simpl a -- Double negation simplification
  Neg (Sum a b) -> Sum (simpl (Neg a)) (simpl (Neg b)) -- Distribute negation over sum
  Neg (Prod a b) -> Prod (simpl (Neg a)) (simpl (Neg b)) -- Distribute negation over product
  Neg (Pow a b) -> Pow (simpl (Neg a)) (simpl b) -- Distribute negation over base of power
  Neg (Inv a) -> Inv (simpl (Neg a)) -- Distribute negation over inversion
  Neg v -> Neg (simpl v)
  -- Logarithm rules
  Log (Real 1) _ -> Real 0 -- Logarithm base 1 of anything is 0
  Log _ (Real 1) -> Real 0 -- Logarithm base anything of 1 is 0
  Ln (Real 1) -> Real 0 -- Natural logarithm of 1 is 0
  -- List rules
  List lst -> List (map simpl lst)
  _ -> expr

-- | Repeatedly applies 'simpl' until the expression no longer changes.
simplRep :: Expr -> Expr
simplRep expr = let s = simpl expr in if s == expr then s else simplRep s

testSimplRep :: Test
testSimplRep =
  TestList
    [ TestCase $ do
        let expected = Real 42
        let actual = simplRep (Real 42)
        assertEqual "Simplification of a numeric constant" expected actual,
      TestCase $ do
        let expected = Real 5
        let actual = simplRep (Sum (Real 5) (Real 0))
        assertEqual "Simplification involving zero" expected actual,
      TestCase $ do
        let expected = Prod (Real 3) (Pow (Var "x") (Real 2))
        let actual = simplRep (Prod (Prod (Real 1) (Real 3)) (Pow (Var "x") (Real 2)))
        assertEqual "Simplification involving multiplication and power" expected actual,
      TestCase $ do
        let expected = Real 2
        let actual = simplRep (Sum (Real 1) (Neg (Neg (Neg (Neg (Real 1))))))
        assertEqual "Simplification involving multiple negations" expected actual,
      TestCase $ do
        let expected = Pow (Sum (Var "x") (Real 4)) (Real 2)
        let actual = simplRep (Pow (Sum (Var "x") (Sum (Real 1) (Real 3))) (Prod (Real 2) (Sum (Real 0) (Real 1))))
        assertEqual "Simplification involving powers" expected actual
    ]

-- | Calculates the derivative of the expression with respect to the given variable.
deriv :: String -> Expr -> Expr
deriv var expr = case expr of
  Var v
    | v == var -> Real 1 -- Derivative of the variable with respect to itself is 1
    | otherwise -> Real 0 -- Derivative of a constant with respect to any variable is 0
  Real _ -> Real 0 -- Derivative of a constant with respect to any variable is 0
  Sum a b -> Sum (deriv var a) (deriv var b)
  Neg a -> Neg (deriv var a)
  Prod a b ->
    Sum (Prod (deriv var a) b) (Prod a (deriv var b))
  Pow base expo ->
    Prod expo (Prod (Pow base (sub expo (Real 1))) (deriv var base))
  Inv a -> Neg (ldiv (deriv var a) (Pow a (Real 2)))
  List list -> List (map simplRep list)
  Log _ arg -> Prod (ldiv (Real 1) (Prod arg (Ln arg))) (deriv var arg)
  Ln arg -> ldiv (deriv var arg) arg

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
    fact n = product [1 .. n]

    sumTerms :: Int -> Expr
    sumTerms n
      | n > deg = Real 0
      | otherwise = Sum (term n) (sumTerms (n + 1))

    term :: Int -> Expr
    term n =
      let coef = Real (1 / fact (fromIntegral n))
          offset = sub (Var var) (Real center)
          powerTerm = Pow offset (Real (fromIntegral n))
          nthDeriv = repl (derivN n var expr) (Var var) (Real center)
       in Prod (Prod nthDeriv coef) powerTerm

-- | Test cases for the 'series' function.
testSeries :: Test
testSeries =
  TestList
    [ TestCase $ do
        let expected = Sum (Real (-2)) (Sum (Prod (Real (-2)) (Sum (Var "x") (Real (-1)))) (Pow (Sum (Var "x") (Real (-1))) (Real 2)))
        let actual = series (Sum (Pow (Var "x") (Real 2)) (Sum (Prod (Real (-4)) (Var "x")) (Real 1))) "x" 1 2
        assertEqual "Taylor series expansion of x^2 - 4x + 1 at center x = 1, degree = 2" expected (simplRep actual),
      TestCase $ do
        let expected = Sum (Real 4) (Sum (Prod (Real 3) (Pow (sub (Var "x") (Real 2)) (Real 2))) (Pow (sub (Var "x") (Real 2)) (Real 3)))
        let actual = series (Sum (Pow (Var "x") (Real 3)) (Sum (Prod (Real (-3)) (Pow (Var "x") (Real 2))) (Real 4))) "x" 2 3
        assertEqual "Taylor series expansion of x^3 - 3x^2 + 4 at center x = 2, degree = 3" expected (simplRep actual)
    ]

mathf :: Expr -> String
mathf expr = case expr of
  Sum a b -> "(" ++ mathf a ++ " + " ++ mathf b ++ ")"
  Real x -> show x
  Neg a -> "-(" ++ mathf a ++ ")"
  Prod a b -> "(" ++ mathf a ++ " * " ++ mathf b ++ ")"
  Var v -> v
  Pow a b -> "(" ++ mathf a ++ "^" ++ mathf b ++ ")"
  Inv a -> "(1 / " ++ mathf a ++ ")"
  List lst -> "[" ++ intercalate ", " (map mathf lst) ++ "]" -- Using curly braces for lists
  Log base expr' -> "log(" ++ mathf base ++ ", " ++ mathf expr' ++ ")"
  Ln expr' -> "ln(" ++ mathf expr' ++ ")"

-- Test cases for math formatting
testMathf :: Test
testMathf =
  TestList
    [ TestCase $ do
        let expected = "x"
        let actual = mathf (Var "x")
        assertEqual "Variable expression formatting" expected actual,
      TestCase $ do
        let expected = "-(y)"
        let actual = mathf (Neg (Var "y"))
        assertEqual "Negation expression formatting" expected actual,
      TestCase $ do
        let expected = "(3.14 * z)"
        let actual = mathf (Prod (Real 3.14) (Var "z"))
        assertEqual "Product expression formatting" expected actual,
      TestCase $ do
        let expected = "[1.0, 2.0, 3.0]"
        let actual = mathf (List [Real 1, Real 2, Real 3])
        assertEqual "List expression formatting" expected actual,
      TestCase $ do
        let expected = "log(a, (x^2.0))"
        let actual = mathf (Log (Var "a") (Pow (Var "x") (Real 2)))
        assertEqual "Logarithm expression formatting" expected actual,
      TestCase $ do
        let expected = "ln(y)"
        let actual = mathf (Ln (Var "y"))
        assertEqual "Natural logarithm expression formatting" expected actual,
      TestCase $ do
        let expected = "(x + y)"
        let actual = mathf (Sum (Var "x") (Var "y"))
        assertEqual "Sum expression formatting" expected actual,
      TestCase $ do
        let expected = "((x^2.0) * (y^3.0))"
        let actual = mathf (Prod (Pow (Var "x") (Real 2)) (Pow (Var "y") (Real 3)))
        assertEqual "Product of powers expression formatting" expected actual,
      TestCase $ do
        let expected = "log((a * b), (x^2.0))"
        let actual = mathf (Log (Prod (Var "a") (Var "b")) (Pow (Var "x") (Real 2)))
        assertEqual "Logarithm with product expression formatting" expected actual,
      TestCase $ do
        let expected = "-(ln(z))"
        let actual = mathf (Neg (Ln (Var "z")))
        assertEqual "Negation of natural logarithm expression formatting" expected actual,
      TestCase $ do
        let expected = "(log(c, d) + ln(e))"
        let actual = mathf (Sum (Log (Var "c") (Var "d")) (Ln (Var "e")))
        assertEqual "Sum of logarithm and natural logarithm expression formatting" expected actual,
      TestCase $ do
        let expected = "(x^(y + z))"
        let actual = mathf (Pow (Var "x") (Sum (Var "y") (Var "z")))
        assertEqual "Exponent with sum formatting" expected actual,
      TestCase $ do
        let expected = "(x^(y * z))"
        let actual = mathf (Pow (Var "x") (Prod (Var "y") (Var "z")))
        assertEqual "Exponent with product formatting" expected actual,
      TestCase $ do
        let expected = "(x^(1 / z))"
        let actual = mathf (Pow (Var "x") (Inv (Var "z")))
        assertEqual "Exponent with inverse formatting" expected actual,
      TestCase $ do
        let expected = "(x^-(ln(y)))"
        let actual = mathf (Pow (Var "x") (Neg (Ln (Var "y"))))
        assertEqual "Exponent with negation and natural logarithm formatting" expected actual,
      TestCase $ do
        let expected = "log(a, (x^(y^2.0)))"
        let actual = mathf (Log (Var "a") (Pow (Var "x") (Pow (Var "y") (Real 2))))
        assertEqual "Exponent with nested power and logarithm formatting" expected actual
    ]

-- Define the test cases for logarithmic operations.
testLogarithm :: Test
testLogarithm =
  TestList
    [ TestCase $ do
        let expected = Real 0
        let actual = simpl (Log (Real 1) (Var "x"))
        assertEqual "Logarithm base 1 of anything is 0" expected actual,
      TestCase $ do
        let expected = Real 0
        let actual = simpl (Log (Var "x") (Real 1))
        assertEqual "Logarithm base anything of 1 is 0" expected actual,
      TestCase $ do
        let expected = Real 0
        let actual = simpl (Ln (Real 1))
        assertEqual "Natural logarithm of 1 is 0" expected actual,
      TestCase $ do
        let expected = Log (Var "a") (Var "b")
        let actual = simpl (Log (Var "a") (Var "b"))
        assertEqual "No simplification when base and argument are not 1" expected actual
    ]

main :: IO ()
main = do
  result <-
    runTestTT
      ( TestList
          [ TestLabel "Taylor series tests" testSeries,
            TestLabel "Simplification tests" testSimplRep,
            TestLabel "Math formatting tests" testMathf,
            TestLabel "Logarithm tests" testLogarithm
          ]
      )
  if failures result > 0 then Exit.exitFailure else Exit.exitSuccess