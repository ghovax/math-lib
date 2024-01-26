import qualified System.Exit as Exit
import Test.HUnit

-- import Data.Complex

data Expr
  = Real Double
  | Complex Double Double
  | Var String
  | Sum Expr Expr
  | Prod Expr Expr
  | Div Expr Expr
  | Func String [Expr]
  | Neg Expr
  deriving (Show, Eq)

-- | Compute the derivative of an expression with respect to a variable.
deriv :: Expr -> String -> Expr
deriv (Real _) _ = Real 0
deriv (Complex _ _) _ = Complex 0 0
deriv (Var v) x
  | v == x = Real 1
  | otherwise = Real 0
deriv (Sum e1 e2) x = Sum (deriv e1 x) (deriv e2 x)
deriv (Prod e1 e2) x = Sum (Prod (deriv e1 x) e2) (Prod e1 (deriv e2 x))
deriv (Div e1 e2) x =
  Div
    ( Sum
        (Prod (deriv e1 x) e2)
        (Neg (Prod e1 (deriv e2 x)))
    )
    (Prod e2 e2)
deriv (Func name args) x = Func name (map (`deriv` x) args)
deriv (Neg e) x = Neg (deriv e x)

-- | Simplify an expression by applying algebraic simplifications.
simpl :: Expr -> Expr
simpl (Real n) = Real n
simpl (Complex r i) = Complex r i
simpl (Var v) = Var v
simpl (Sum e1 e2) =
  let simplE1 = simpl e1
      simplE2 = simpl e2
   in case (simplE1, simplE2) of
        (Real 0, _) -> simplE2 -- If the first expression is 0, return the second expression
        (_, Real 0) -> simplE1 -- If the second expression is 0, return the first expression
        (Real n1, Real n2) -> Real (n1 + n2)
        (Complex r1 i1, Complex r2 i2) -> Complex (r1 + r2) (i1 + i2)
        _ -> Sum simplE1 simplE2
simpl (Prod e1 e2) =
  let simplE1 = simpl e1
      simplE2 = simpl e2
   in case (simplE1, simplE2) of
        (Real n1, Real n2) -> Real (n1 * n2)
        (Complex r1 i1, Complex r2 i2) -> Complex (r1 * r2 - i1 * i2) (r1 * i2 + i1 * r2)
        (Real 0, _) -> Real 0
        (_, Real 0) -> Real 0
        (Real 1, e) -> e
        (e, Real 1) -> e
        _ -> Prod simplE1 simplE2
simpl (Div e1 e2) =
  let simplE1 = simpl e1
      simplE2 = simpl e2
   in case (simplE1, simplE2) of
        (_, Real 0) -> error "Division by zero"
        (Real 0, _) -> Real 0
        (e, Real 1) -> e
        _ -> Div simplE1 simplE2
simpl (Func name args) = Func name (map simpl args)
simpl (Neg e) =
  case simpl e of
    Real n -> Real (-n)
    (Complex r i) -> Complex (-r) (-i)
    s -> Neg s

-- | Test cases for the 'deriv' function.
testDeriv :: Test
testDeriv =
  TestList
    [ TestCase $
        assertEqual
          "Derivation of simple expression"
          (simpl (deriv (Prod (Real 2) (Var "x")) "x"))
          (Real 2),
      TestCase $
        assertEqual
          "Derivation with respect to different variables"
          (simpl (deriv (Sum (Var "x") (Var "y")) "y"))
          (Real 1),
      TestCase $
        assertEqual
          "Derivation of product of two functions"
          (simpl (deriv (Prod (Func "f" [Var "x"]) (Func "g" [Var "x"])) "x"))
          ( Sum
              (Prod (deriv (Func "f" [Var "x"]) "x") (Func "g" [Var "x"]))
              (Prod (Func "f" [Var "x"]) (deriv (Func "g" [Var "x"]) "x"))
          ),
      TestCase $
        assertEqual
          "Derivation of complex expression"
          (simpl (deriv (Prod (Sum (Real 2) (Var "x")) (Div (Var "y") (Var "z"))) "x"))
          (Div (Var "y") (Var "z"))
    ]

-- | Test cases for the 'simpl' function.
testSimpl :: Test
testSimpl =
  TestList
    [ TestCase $
        assertEqual
          "Simplify addition"
          (simpl (Sum (Real 2) (Real 3)))
          (Real 5),
      TestCase $
        assertEqual
          "Simplify multiplication"
          (simpl (Prod (Real 2) (Var "x")))
          (Prod (Real 2) (Var "x")),
      TestCase $
        assertEqual
          "Simplify function"
          (simpl (Func "f" [Var "x"]))
          (Func "f" [Var "x"]),
      TestCase $
        assertEqual
          "Simplify complex expression"
          (simpl (Sum (Prod (Real 3) (Var "x")) (Prod (Sum (Real 2) (Var "y")) (Real 4))))
          (Sum (Prod (Real 3) (Var "x")) (Prod (Sum (Real 2) (Var "y")) (Real 4)))
    ]

-- | Run all test cases.
main :: IO ()
main = do
  result <- runTestTT (TestList [TestLabel "Simplification tests" testSimpl, TestLabel "Derivation tests" testDeriv])
  if failures result > 0 then Exit.exitFailure else Exit.exitSuccess