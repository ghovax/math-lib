import Data.Functor.Identity (Identity)
import Text.Parsec
import Text.Parsec.Expr
import Text.Parsec.String (Parser)

data Expr
  = Num Double
  | Var String
  | Sum Expr Expr
  | Prod Expr Expr
  | Div Expr Expr
  deriving (Show)

-- Define a helper function to consume trailing whitespace
lexeme :: Parser a -> Parser a
lexeme p = p <* spacesLoc
  where
    spacesLoc = many (oneOf " \t") -- Consume spaces and tabs

-- Compute derivatives
derivative :: Expr -> String -> Expr
derivative (Num _) _ = Num 0
derivative (Var v) x
  | v == x = Num 1
  | otherwise = Num 0
derivative (Sum e1 e2) x = Sum (derivative e1 x) (derivative e2 x)
derivative (Prod e1 e2) x = Sum (Prod (derivative e1 x) e2) (Prod e1 (derivative e2 x))
derivative (Div e1 e2) x = Div (Sum (Prod (derivative e1 x) e2) (neg (Prod e1 (derivative e2 x)))) (Prod e2 e2)

-- Define unary negation
neg :: Expr -> Expr
neg = Prod (Num (-1))

-- Define a helper function to parse integer and floating-point numbers
number :: Parser Double
number = lexeme $ read <$> many1 digit <* optional (char '.' >> many digit)

-- Define a helper function to parse variables (e.g., "x", "y")
variable :: Parser String
variable = lexeme $ many1 letter

-- Define a parser for expressions
expr :: Parser Expr
expr = term `chainl1` addOp

-- Define a term parser
term :: Parser Expr
term = factor `chainl1` mulOp

-- Define a factor parser
factor :: Parser Expr
factor = lexeme $ parens expr <|> Var <$> variable <|> Num <$> number

-- Define addition operator
addOp :: Parser (Expr -> Expr -> Expr)
addOp = reservedOp "+" >> return Sum

-- Define multiplication and division operators
mulOp :: Parser (Expr -> Expr -> Expr)
mulOp =
  do
    reservedOp "*"
    return Prod
    <|> do
      reservedOp "/"
      return Div

-- Define a helper function to parse parentheses
parens :: Parser a -> Parser a
parens = between (lexeme $ char '(') (lexeme $ char ')')

-- Define a helper function to parse reserved operators
reservedOp :: String -> Parser ()
reservedOp op = lexeme $ do
  _ <- string op
  notFollowedBy (oneOf "+-*/")

-- Parse an expression
parseExpr :: String -> Either ParseError Expr
parseExpr = parse (lexeme expr) ""

-- Pretty print an expression
prettyPrint :: Expr -> String
prettyPrint (Num n) = show n
prettyPrint (Var v) = v
prettyPrint (Sum e1 e2) = "(" ++ prettyPrint e1 ++ " + " ++ prettyPrint e2 ++ ")"
prettyPrint (Prod e1 e2) = "(" ++ prettyPrint e1 ++ " * " ++ prettyPrint e2 ++ ")"
prettyPrint (Div e1 e2) = "(" ++ prettyPrint e1 ++ " / " ++ prettyPrint e2 ++ ")"

-- Simplify an expression
simplify :: Expr -> Expr
simplify (Num n) = Num n
simplify (Var v) = Var v
simplify (Sum e1 e2) =
  let simplifiedE1 = simplify e1
      simplifiedE2 = simplify e2
   in case (simplifiedE1, simplifiedE2) of
        (Num n1, Num n2) -> Num (n1 + n2)
        _ -> Sum simplifiedE1 simplifiedE2
simplify (Prod e1 e2) =
  let simplifiedE1 = simplify e1
      simplifiedE2 = simplify e2
   in case (simplifiedE1, simplifiedE2) of
        (Num n1, Num n2) -> Num (n1 * n2)
        (Num 0, _) -> Num 0
        (_, Num 0) -> Num 0
        (Num 1, e) -> e
        (e, Num 1) -> e
        _ -> Prod simplifiedE1 simplifiedE2
simplify (Div e1 e2) =
  let simplifiedE1 = simplify e1
      simplifiedE2 = simplify e2
   in case (simplifiedE1, simplifiedE2) of
        (_, Num 0) -> error "Division by zero"
        (Num 0, _) -> Num 0
        (e, Num 1) -> e
        _ -> Div simplifiedE1 simplifiedE2

main :: IO ()
main = do
  let input = "3*x + (2 + y) * 4"
  case parseExpr input of
    Left err -> putStrLn $ "Error: " ++ show err
    Right result -> do
      putStrLn $ "Parsed: " ++ show result
      let var = "x"
      let resultDerivative = derivative result var
      putStrLn $ "Derivative with respect to " ++ var ++ ": " ++ show resultDerivative
      let simplifiedDerivative = simplify resultDerivative
      putStrLn $ "Simplified derivative: " ++ prettyPrint simplifiedDerivative
