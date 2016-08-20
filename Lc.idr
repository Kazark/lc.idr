module Lc

%default total

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

----------------------------------------------------------------------------------

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
  | UnexpectedTermination
  | UnexpectedToken Token

ParserResult : Type
ParserResult = ParseResult ParserError (Expr, Nat)

parseAbstraction : List Token -> Either ParserResult (Nat, Expr -> Expr)
parseAbstraction ((VarTok _) :: ((VarTok _) :: _)) = Left $ FailedWith AdvancedSyntaxNotImplemented
parseAbstraction ((VarTok x) :: (Dot :: xs)) = Right (2, Abstraction x)
parseAbstraction (x :: _) = Left $ FailedWith $ UnexpectedToken x
parseAbstraction [] = Left $ FailedWith UnexpectedTermination

parseExpr : List Token -> ParserResult
parseExpr ((VarTok x) :: _) = Found (Variable x, 1)
parseExpr (Lambda :: xs) =
  case parseAbstraction xs of
    Right (skip, mkExpr) =>
      case xs of
        _ :: _ :: xs' =>
          case parseExpr xs' of
            Found (expr, skip2) => Found (mkExpr expr, skip + skip2)
            FailedWith error => FailedWith error
        _ => FailedWith UnexpectedTermination
    Left result => result
parseExpr (OpenParen :: xs) = ?asdf
  --case parseExpr xs of
  --  Found (expr1, skip) =>
  --    case parseExpr $ drop skip xs of
  --      Found (expr2, skip2) =>
  --        case drop (skip + skip2) xs of
  --          (CloseParen :: xs) => Found (Application expr1 expr2, skip + skip2 + 1)
  --          _ => FailedWith FailedToMatchCloseParen
  --      FailedWith error => FailedWith error
  --  FailedWith error => FailedWith error
parseExpr [] = FailedWith UnexpectedTermination
parseExpr (x :: _) = FailedWith $ UnexpectedToken x

parseTokens : List Token -> ParseResult ParserError Expr
parseTokens [] = FailedWith NoTokens
parseTokens xs@(_ :: _) =
  case parseExpr xs of
    Found (expr, skip) =>
      case drop skip xs of
        [] => Found expr
        xs => FailedWith $ TrailingCharacters xs
    FailedWith error => FailedWith error

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

bound : Expr -> List Char
bound (Variable _) = []
bound (Abstraction x y) = x :: bound y
bound (Application x y) = bound x ++ bound y

