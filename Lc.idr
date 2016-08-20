module Lc

%default total

-- Lambda expressions are composed of:
-- 
--     variables v1, v2, ..., vn, ...
--     the abstraction symbols lambda 'λ' and dot '.'
--     parentheses ( )
-- 
data Token =
  VarTok Char
  | Lambda
  | Dot
  | OpenParen
  | CloseParen

data ParseResult a b = Found b | FailedWith a

data TokenizeError = TokenizeErr

TokenizerResult : Type
TokenizerResult = ParseResult TokenizeError Token

tokenizeChar : Char -> TokenizerResult
tokenizeChar '(' = Found OpenParen
tokenizeChar ')' = Found CloseParen
tokenizeChar '^' = Found Lambda
tokenizeChar '.' = Found Dot
tokenizeChar x = Found $ VarTok x

-- applicatve?
shortCircuit : ParseResult a b -> ParseResult a (List b) -> ParseResult a (List b)
shortCircuit (Found x) (Found acc) = Found $ x :: acc
shortCircuit _ (FailedWith x) = FailedWith x
shortCircuit (FailedWith x) _ = FailedWith x

tokenize : String -> ParseResult TokenizeError (List Token)
tokenize = compactResult . tokenizeEach . unpack where
  tokenizeEach : List Char -> List TokenizerResult
  tokenizeEach = map tokenizeChar . filter (/= ' ')
  compactResult : List TokenizerResult -> ParseResult TokenizeError (List Token)
  compactResult = foldr shortCircuit $ Found []

-- The set of lambda expressions, Expr, can be defined inductively:
-- 
--     If x is a variable, then x : Expr
--     If x is a variable and M : Expr, then (\x.M) : Expr
--     If M, N : Expr, then (M N) : Expr
-- 
-- Instances of rule 2 are known as abstractions and instances of rule 3 are known as applications.[14]

data Expr =
  Variable Char
  | Abstraction Char Expr
  | Application Expr Expr

data ParserError =
  NoTokens
  | AdvancedSyntaxNotImplemented
  | FailedToMatchCloseParen
  | TrailingCharacters (List Token)
  | BubbledUpTokenizeError TokenizeError
  | ExpressionTerminatedUnexpectedly
  | UnexpectedToken Token

ParserResult : Type
ParserResult = ParseResult ParserError (Expr, List Token)

mutual
  partial
  parseExpr : List Token -> ParserResult
  parseExpr ((VarTok x) :: xs) = Found (Variable x, xs)
  parseExpr (Lambda :: xs) = parseAbstraction xs
  parseExpr (OpenParen :: xs) = parseApplication xs
  parseExpr [] = FailedWith ExpressionTerminatedUnexpectedly
  parseExpr (x :: _) = FailedWith $ UnexpectedToken x

  partial
  parseAbstraction : List Token -> ParserResult
  parseAbstraction ((VarTok _) :: ((VarTok _) :: _)) = FailedWith AdvancedSyntaxNotImplemented
  parseAbstraction ((VarTok x) :: (Dot :: xs)) =
    case parseExpr xs of
      Found (expr, remainder) => Found (Abstraction x expr, remainder)
      FailedWith error => FailedWith error
  parseAbstraction (x :: _) = FailedWith $ UnexpectedToken x

  partial
  parseApplication : List Token -> ParserResult
  parseApplication xs =
    case parseExpr xs of
      Found (expr1, remainder1) =>
        case parseExpr remainder1 of
          Found (expr2, CloseParen :: remainder2) => Found (Application expr1 expr2, remainder2)
          Found (_, _) => FailedWith FailedToMatchCloseParen
          FailedWith error => FailedWith error
      FailedWith error => FailedWith error

partial
parseTokens : List Token -> ParseResult ParserError Expr
parseTokens [] = FailedWith NoTokens
parseTokens ((VarTok x) :: []) = Found $ Variable x
parseTokens (Lambda :: (_ :: _)) = FailedWith AdvancedSyntaxNotImplemented
parseTokens (OpenParen :: xs) =
  case parseApplication xs of
    Found (expr, []) => Found expr
    Found (expr, x) => FailedWith $ TrailingCharacters x
    FailedWith error => FailedWith error
parseTokens (x :: (_ :: _)) = FailedWith $ UnexpectedToken x

partial
parse : String -> ParseResult ParserError Expr
parse code = 
  case tokenize code of
    Found tokens => parseTokens tokens
    FailedWith x => FailedWith $ BubbledUpTokenizeError x

-- Future:
-- 
-- To keep the notation of lambda expressions uncluttered, the following conventions are usually applied:
-- 
--     Outermost parentheses are dropped: M N instead of (M N)
--     Applications are assumed to be left associative: M N P may be written instead of ((M N) P)[15]
--     The body of an abstraction extends as far right as possible: λx.M N means λx.(M N) and not (λx.M) N
--     A sequence of abstractions is contracted: λx.λy.λz.N is abbreviated as λxyz.N[16][17]

bound' : Expr -> List Char
bound' (Variable _) = []
bound' (Abstraction x y) = x :: bound' y
bound' (Application x y) = bound' x ++ bound' y

partial
bound : (code : String) -> ParseResult ParserError (List Char)
bound code =
  case parse code of
    Found expr => Found $ bound' expr
    FailedWith error => FailedWith error

