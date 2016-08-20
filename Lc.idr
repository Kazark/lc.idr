module Lc

import Smaller

%default total

data Token =
  VarTok Char
  | Lambda
  | Dot
  | OpenParen
  | CloseParen

data ParseResult a b = Found b | FailedWith a

ListParser : Type -> Type -> Type -> Type
ListParser e i o = (inList : List i) -> ParseResult e (o, (smallL : List i ** Smaller smallL inList))

----------------------------------------------------------------------------------

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
  | ExpressionTerminatedUnexpectedly
  | UnexpectedToken Token

TokenListParser : Type
TokenListParser = ListParser ParserError Token Expr

mutual
  parseExpr : TokenListParser
  parseExpr xs@(VarTok x :: _) = Found (Variable x, peelOff xs)
  parseExpr (Lambda :: xs) =
    case parseAbstraction xs of
      Found (x, remainder) => Found (x, consToType Lambda remainder)
      FailedWith error => FailedWith error
  parseExpr (OpenParen :: xs) =
    case parseApplication xs of
      Found (x, remainder) => Found (x, consToType OpenParen remainder)
      FailedWith error => FailedWith error
  parseExpr [] = FailedWith ExpressionTerminatedUnexpectedly
  parseExpr (x :: _) = FailedWith $ UnexpectedToken x

  parseAbstraction : TokenListParser
  parseAbstraction (VarTok _ :: VarTok _ :: _) = FailedWith AdvancedSyntaxNotImplemented
  parseAbstraction (VarTok x :: Dot :: xs) =
    case parseExpr xs of
      Found (expr, remainder) => Found (Abstraction x expr, appendToType [VarTok x, Dot] remainder)
      FailedWith error => FailedWith error
  parseAbstraction (x :: _) = FailedWith $ UnexpectedToken x
  parseAbstraction [] = FailedWith ExpressionTerminatedUnexpectedly

  asdf : (expr1 : Expr) -> TokenListParser

  parseApplication : TokenListParser
  parseApplication xs =
    case parseExpr xs of
      Found (expr1, (remainder1 ** _)) => asdf expr1 remainder1
      --  case parseExpr remainder1 of
      --    Found (expr2, ((CloseParen :: remainder2) ** prf)) => Found (Application expr1 expr2, (remainder2 ** ?need_tis_proof2))
      --    Found (_, _) => FailedWith FailedToMatchCloseParen
      --    FailedWith error => FailedWith error
      FailedWith error => FailedWith error

partial
parseTokens : List Token -> ParseResult ParserError Expr
parseTokens [] = FailedWith NoTokens
parseTokens ((VarTok x) :: []) = Found $ Variable x
parseTokens (Lambda :: (_ :: _)) = FailedWith AdvancedSyntaxNotImplemented
--parseTokens (OpenParen :: xs) =
--  case parseApplication xs of
--    Found (expr, []) => Found expr
--    Found (expr, x) => FailedWith $ TrailingCharacters x
--    FailedWith error => FailedWith error
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

bound : Expr -> List Char
bound (Variable _) = []
bound (Abstraction x y) = x :: bound y
bound (Application x y) = bound x ++ bound y

