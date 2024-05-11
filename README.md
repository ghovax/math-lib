# math-lib

`math-lib` is a Haskell library for manipulating mathematical expressions represented 
by the `Expr` data type. It provides functions for various operations on expressions.

## Example

```haskell
-- Define an expression: (x^2) + (3 * x)
let expr = Sum (Pow (Var "x") (Real 2)) (Prod (Real 3) (Var "x"))

-- Simplify the expression
let simplifiedExpr = simpl expr

-- Calculate the derivative with respect to 'x'
let derivativeExpr = simplRep (deriv "x" simplifiedExpr)
```

## Functions and data types

| Function   | Description |
|------------|-------------|
| `sub`      | Subtraction operation |
| `ldiv`     | Left division operation |
| `rdiv`     | Right division operation |
| `repl`     | Expression substitution |
| `replAll`  | Replace all occurrences in an expression |
| `simpl`    | Simplify expressions by evaluating constants |
| `simplRep` | Repeatedly apply simplification until no change |
| `deriv`    | Calculate the derivative of an expression |
| `derivN`   | Calculate the n-th derivative of an expression |
| `series`   | Evaluate a Taylor series for an expression |

The `Expr` data type represents mathematical expressions in Haskell.

| Constructor | Description |
|-------------|-------------|
| `Sum`       | Sum of two expressions |
| `Real`      | Numeric constant |
| `Neg`       | Negation of an expression |
| `Prod`      | Product of two expressions |
| `Var`       | Variable |
| `Pow`       | Exponentiation of one expression to another |
| `Inv`       | Inversion of an expression |
| `List`      | List of expressions |
| `Log`       | Logarithm of an expression to a given base |
| `Ln`        | Natural logarithm of an expression |

## Disclaimer

The tests for the `series` function are still failing, I'll fix it soon enough.