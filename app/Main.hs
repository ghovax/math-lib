import qualified System.Exit as Exit
import Test.HUnit

-- |
-- Module      : Main
-- Description : Provides operations for manipulating the `Expr` data type.
--
-- This module defines various operations on the `Expr` data type, including
-- substitution, simplification, and repeated simplification.
--
-- What I am doing by constructing the `Expr` datatype is making it possible
-- to have trees of expressions and then defining functions that respect a set
-- of rules when traversing them. For instance in the `repl` function when I go
-- to define how we should replace the terms in a sum, I specify that we should
-- replace each component of the sum individually. This in a sense is making
-- `Sum` transparent to the replacement operation, but this also happens with
-- the multiplication operator `Prod` and with the power operator `Pow`.
data Expr
  = -- Binary operators
    Sum Expr Expr
  | Prod Expr Expr
  | Pow Expr Expr
  | -- Core elements
    Real Double
  | List [Expr]
  | Var String
  | -- Unary operators
    Neg Expr
  | Inv Expr
  | -- Other functions
    Log Expr Expr
  | Ln Expr
  deriving (Show, Eq)

-- | Subtracts expression `b` from `a`.
sub :: Expr -> Expr -> Expr
sub a b = Sum a (Neg b)

-- | Left division: divides expression `a` by `b`.
ldiv :: Expr -> Expr -> Expr
ldiv a b = Prod a (Inv b)

-- | Right division: divides expression `b` by `a`.
rdiv :: Expr -> Expr -> Expr
rdiv a b = Prod (Inv a) b

-- | Replaces occurrences of `targ` with `rule` in the expression.
repl :: Expr -> Expr -> Expr -> Expr
repl expr targ rule = case expr of
  -- Propagate the replacement through the constituents
  -- Binary operators
  Sum a b -> Sum (repl a targ rule) (repl b targ rule)
  Prod a b -> Prod (repl a targ rule) (repl b targ rule)
  Pow a b -> Pow (repl a targ rule) (repl b targ rule)
  -- Unary operators
  Neg a -> Neg (repl a targ rule)
  Inv a -> Inv (repl a targ rule)
  -- Core elements
  Var v -> case targ of
    Var x | x == v -> rule -- When dispatching over a variable, verify if we need to do a variable replacement
    _ -> Var v -- Otherwise, don't change anything
    -- Apply the replacement operation to each element in the list
  List lst -> List (map (\item -> repl item targ rule) lst)
  -- Other functions
  Log base arg -> Log (repl base targ rule) (repl arg targ rule)
  Ln arg -> Ln (repl arg targ rule)
  -- If the pattern matching fails, return the expression itself (no-op)
  _ -> expr

-- | Replaces all occurrences of target expressions with their corresponding rules.
-- Convenience function: just like `repl` but allows for more replacement rules to be applied.
replAll :: Expr -> [(Expr, Expr)] -> Expr
replAll = foldl (\item (targ, rule) -> repl item targ rule)

-- | Simplifies the expression by evaluating subexpressions.
simpl :: Expr -> Expr
simpl expr = case expr of
  -- Sum rules
  Sum (Real 0) a -> simpl a -- 0 + a == a
  Sum a (Real 0) -> simpl a -- a + 0 == a
  Sum a b | a == b -> Prod (Real 2) (simpl a) -- a + a == 2 * a
  Sum (Real a) (Real b) -> Real (a + b) -- Evaluation
  Sum a b -> Sum (simpl a) (simpl b) -- Propagation through the constituents
  -- Product rules
  Prod (Real 0) _a -> Real 0 -- 0 * a == 0
  Prod _a (Real 0) -> Real 0 -- a * 0 == 0
  Prod (Real 1) a -> simpl a -- 1 * a == a
  Prod a (Real 1) -> simpl a -- a * 1 == a
  Prod (Real a) (Real b) -> Real (a * b) -- Evaluation
  Prod a b | a == b -> Pow (simpl a) (Real 2) -- a * a = a^2 with propagation
  Prod a b -> Prod (simpl a) (simpl b) -- Propagation through the constituents
  -- Power rules
  Pow (Real x) (Real 0) | x > 0 -> Real 1 -- x^0 == 1 (for x > 0)
  Pow x (Real 1) -> simpl x -- x^1 == x with propagation
  Pow (Real 1) _x -> Real 1 -- 1^x == 1
  Pow x (Real n)
    -- \| n == 0 -> Real 1 -- x^0 == 1 -- TODO: For any x?
    | n == 1 -> simpl x -- x^1 == x
    -- Pow (Real 0) _x | _x > 0 -> Real 0 -- TODO: 0^x == 0 (for x > 0)
  Pow (Real a) (Real b) -> Real (a ** b) -- Evaluation
  Pow base expo -> Pow (simpl base) (simpl expo) -- Propagation through the constituents
  -- Negation rules
  Neg (Real x) -> Real (-x) -- Evaluation
  Neg (Neg a) -> simpl a -- -(-a) == a
  Neg (Sum a b) -> Sum (simpl (Neg a)) (simpl (Neg b)) -- -(a + b) == (-a) + (-b) with simplification
  Neg (Prod a b) -> Prod (simpl (Neg a)) (simpl b) -- -(a * b) == (-a) * b with simplification
  Neg (Pow a b) -> Pow (simpl (Neg a)) (simpl b) -- -(a^b) == (-a)^b with simplification
  Neg (Inv a) -> Inv (simpl (Neg a)) -- -(a^-1) == (-a)^-1 with simplification
  Neg v -> Neg (simpl v) -- Propagation through the constituent
  -- Logarithm rules
  Log (Real 1) _x -> Real 0 -- log_1(x) == 0 -- TODO: Shouldn't there be any conditions on x?)
  Log _b (Real 1) -> Real 0 -- log_b(1) == 0
  Ln (Real 1) -> Real 0 -- ln(1) == 0
  -- List rules
  List lst -> List (map simpl lst) -- Propagate the simplification through all the constituents of the list
  -- If the pattern matching fails, return the expression itself (no-op)
  _ -> expr

-- | Repeatedly applies `simpl` until the expression no longer changes.
simplRep :: Expr -> Expr
simplRep expr = let s = simpl expr in if s == expr then s else simplRep s

-- Test cases for the `simplRep` function
testSimplRep :: Test
testSimplRep =
  TestList
    [ TestCase $ do
        let expected = Real 42
        let actual = simplRep (Real 42)
        assertEqual "42 == 42" expected actual,
      --
      TestCase $ do
        let expected = Real 5
        let actual = simplRep (Sum (Real 5) (Real 0))
        assertEqual "5 + 0 == 5" expected actual,
      --
      TestCase $ do
        let expected = Prod (Real 3) (Pow (Var "x") (Real 2))
        let actual = simplRep (Prod (Prod (Real 1) (Real 3)) (Pow (Var "x") (Real 2)))
        assertEqual "(1 * 3) * x^2 == 3 * x^2" expected actual,
      --
      TestCase $ do
        let expected = Real 2
        let actual = simplRep (Sum (Real 1) (Neg (Neg (Neg (Neg (Real 1))))))
        assertEqual "1 + -(-(-(-1))) == 2" expected actual,
      --
      TestCase $ do
        let expected = Pow (Sum (Var "x") (Real 4)) (Real 2)
        let actual = simplRep (Pow (Sum (Var "x") (Sum (Real 1) (Real 3))) (Prod (Real 2) (Sum (Real 0) (Real 1))))
        assertEqual "(x + (1 + 3))^(2 * (0 + 1)) == (x + 4)^2" expected actual
    ]

-- | Calculates the derivative of `expr` with respect to `var`.
deriv :: String -> Expr -> Expr
deriv var expr = case expr of
  -- Core elements
  Var v
    | v == var -> Real 1 -- d/dx(x) == 1
    | otherwise -> Real 0 -- d/dx(y) == 0
  Real _n -> Real 0 -- d/dx(n) == 0
  List list -> List (map (deriv var) list) -- Propagate the derivation through all the elements of the list
  -- Binary operators
  -- They are transparent to the derivation
  Sum a b -> Sum (deriv var a) (deriv var b) -- d/dx(a + b) == d/dx(a) + d/dx(b)
  Prod a b ->
    Sum (Prod (deriv var a) b) (Prod a (deriv var b)) -- d/dx(a * b) == d/dx(a) * b + a * d/dx(b)
  Pow y n ->
    Prod n (Prod (Pow y (sub n (Real 1))) (deriv var y)) -- d/dx(y^n) == n * (y^(n - 1)) * d/dx(y)) -- TODO: Is this correct?
    -- Unary operators
  Neg a -> Neg (deriv var a) -- d/dx(-a) == -d/dx(a)
  Inv a -> Neg (ldiv (deriv var a) (Pow a (Real 2))) -- d/dx(a) == -(d/dx(a) / a^2) -- TODO: Is this correct?
  -- Other functions -- TODO: Undocumented functions!
  Log _ arg -> Prod (ldiv (Real 1) (Prod arg (Ln arg))) (deriv var arg)
  Ln arg -> ldiv (deriv var arg) arg

-- | Calculates the n-th derivative of the expression with respect to the given variable.
derivN :: Int -> String -> Expr -> Expr
derivN 0 _var expr = expr
derivN n var expr = derivN (n - 1) var (deriv var expr)

-- | Evaluates a Taylor series for `expr`, with respect to `var`, centered at `center`, and of degree `deg`.
series :: Expr -> String -> Double -> Int -> Expr
series expr var center deg = sumTerms 0
  where
    -- Calculates the n-th factorial -- TODO: Implement caching in order to speed up
    fact :: Int -> Int
    fact n = product [1 .. n]

    -- Calculate the partial sum of degree `n`
    sumTerms :: Int -> Expr
    sumTerms n
      | n > deg = Real 0
      | otherwise = Sum (term n) (sumTerms (n + 1))

    -- Iteratively calculate successive terms of the sum by using the current degree `n`
    term :: Int -> Expr
    term n =
      let coef = Real (1 / fromIntegral (fact n)) -- 1 / n!
          offset = sub (Var var) (Real center) -- x - x_0
          powerTerm = Pow offset (Real (fromIntegral n)) -- (x - x_0)^n
          -- Replace in the n-th derivative of `expr` with respect to `var` the variable
          -- `var` with the center of the series expansion `center`
          nthDeriv = repl (derivN n var expr) (Var var) (Real center)
       in Prod (Prod coef nthDeriv) powerTerm -- (1 / n!)

-- TODO: Make sure the tests are working!

-- | Test cases for the `series` function.
testSeries :: Test
testSeries =
  TestList
    [ TestCase $ do
        let expected = Sum (Real (-2)) (Sum (Prod (Real (-2)) (Sum (Var "x") (Real (-1)))) (Pow (Sum (Var "x") (Real (-1))) (Real 2)))
        let actual = series (Sum (Pow (Var "x") (Real 2)) (Sum (Prod (Real (-4)) (Var "x")) (Real 1))) "x" 1 2
        assertEqual "expr = x^2 + (-4 * x + 1), var = x, center = 1, deg = 2" expected (simplRep actual),
      --
      TestCase $ do
        let expected = Sum (Real 4) (Sum (Prod (Real 3) (Pow (sub (Var "x") (Real 2)) (Real 2))) (Pow (sub (Var "x") (Real 2)) (Real 3)))
        let actual = series (Sum (Pow (Var "x") (Real 3)) (Sum (Prod (Real (-3)) (Pow (Var "x") (Real 2))) (Real 4))) "x" 2 3
        assertEqual "expr = x^3 - (3 * x^2 + 4), var = x, center = 2, deg = 3" expected (simplRep actual)
    ]

-- Define the test cases for logarithmic operations.
testLogarithm :: Test
testLogarithm =
  TestList
    [ TestCase $ do
        let expected = Real 0
        let actual = simplRep (Log (Real 1) (Var "x"))
        assertEqual "log_1(x) == 0" expected actual,
      --
      TestCase $ do
        let expected = Real 0
        let actual = simplRep (Log (Var "x") (Real 1))
        assertEqual "log_x(1) == 0" expected actual,
      --
      TestCase $ do
        let expected = Real 0
        let actual = simplRep (Ln (Real 1))
        assertEqual "ln(1) == 0" expected actual,
      --
      TestCase $ do
        let expected = Log (Var "a") (Var "b")
        let actual = simplRep (Log (Var "a") (Var "b"))
        assertEqual "log_a(b) == log_a(b)" expected actual
    ]

main :: IO ()
main = do
  result <-
    runTestTT
      ( TestList
          [ TestLabel "Taylor series tests" testSeries,
            TestLabel "Repeated simplification tests" testSimplRep,
            TestLabel "Logarithm tests" testLogarithm
          ]
      )
  if failures result > 0 then Exit.exitFailure else Exit.exitSuccess