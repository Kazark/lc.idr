module Lc

%default total
%access public export

data Token
  = LParen
  | RParen
  | Dot
  | Lambda
  | Alpha Char

tokenize : List Char -> List Token
tokenize [] = []
tokenize ('(' :: cs) = LParen :: tokenize cs
tokenize (')' :: cs) = RParen :: tokenize cs
tokenize ('.' :: cs) = Dot :: tokenize cs
tokenize ('^' :: cs) = Lambda :: tokenize cs
tokenize (c :: cs) =
  (if isAlphaNum c
   then [Alpha c]
   else []) ++ tokenize cs

data Term
  = Var Char
  | Func Char Term
  | Appl Term Term

data Interim : Type where
  Error : String -> Interim
  ApplIfRParen : Term -> Term -> Interim
  ArgExpected : Interim
  DotExpected : Char -> Interim
  ApplExpected : Interim
  ParamExpected : Term -> Interim
  BodyExpected : Char -> Interim
  BodyExpectedNested : Char -> Interim -> Interim
  ApplExpectedNested : Interim -> Interim
  ParamExpectedNested : Term -> Interim -> Interim
  ParsedTerm : Term -> Interim

parseOne : Interim -> Token -> Interim
parseOne (Error y) _ = Error y
parseOne (ApplIfRParen t0 t1) RParen = ParsedTerm $ Appl t0 t1
parseOne (ApplIfRParen _ _) _ = Error "expected closing parenthesis"
parseOne ArgExpected (Alpha c) = DotExpected c
parseOne ArgExpected _ = Error "expected but did not find argument"
parseOne (DotExpected c) Dot = BodyExpected c
parseOne (DotExpected c) _ = Error "expected dot"
parseOne ApplExpected (Alpha c) = ParamExpected (Var c)
parseOne ApplExpected LParen = ApplExpectedNested ApplExpected
parseOne ApplExpected Lambda = ApplExpectedNested ArgExpected
parseOne ApplExpected _ = Error "expected application"
parseOne (ParamExpected t) (Alpha c) = ApplIfRParen t (Var c)
parseOne (ParamExpected t) LParen = ParamExpectedNested t ApplExpected
parseOne (ParamExpected t) Lambda = ParamExpectedNested t ArgExpected
parseOne (ParamExpected _) _ = Error "expected parameter"
parseOne (BodyExpected arg) (Alpha b) = ParsedTerm (Func arg (Var b))
parseOne (BodyExpected c) LParen = BodyExpectedNested c ApplExpected
parseOne (BodyExpected c) Lambda = BodyExpectedNested c ArgExpected
parseOne (BodyExpected _) _ = Error "expected parameter"
parseOne (BodyExpectedNested c interim) token =
  case parseOne interim token of
    ParsedTerm term => ParsedTerm $ Func c term
    Error e => Error e
    interim_ => BodyExpectedNested c interim_
parseOne (ApplExpectedNested interim) token =
  case parseOne interim token of
    ParsedTerm term => ParamExpected term
    Error e => Error e
    interim_ => ApplExpectedNested interim_
parseOne (ParamExpectedNested term0 interim) token =
  case parseOne interim token of
    ParsedTerm term1 => ApplIfRParen term0 term1
    Error e => Error e
    interim_ => ParamExpectedNested term0 interim_
parseOne (ParsedTerm _) _ = Error "trailing characters"

parseInterim : List Token -> Interim
parseInterim [] = Error "no valid tokens"
parseInterim (LParen :: xs) = foldl parseOne ApplExpected xs
parseInterim (RParen :: xs) = Error "invalid expression beginning with )"
parseInterim (Dot :: xs) = Error "invalid expression beginning with ."
parseInterim (Lambda :: xs) = foldl parseOne ArgExpected xs
parseInterim ((Alpha x) :: []) = ParsedTerm (Var x)
parseInterim ((Alpha _) :: (_ :: _)) = Error "invalid expression beginning with var"

parse : List Token -> Either String Term
parse toks =
  case parseInterim toks of
       (Error x) => Left x
       (ApplIfRParen _ _) => Left "incomplete application: no end )"
       ArgExpected => Left "incomplete lambda: arg expected"
       (DotExpected _) => Left "incomplete lambda: dot expected"
       ApplExpected => Left "incomplete application: nothing after ("
       (ParamExpected _) => Left "incomplete application: expecting parameter"
       (BodyExpected _) => Left "incomplete lambda: body expected"
       (BodyExpectedNested _ _) => Left "incomplete lambda: nested body incomplete"
       (ApplExpectedNested _) => Left "incomplete application: first expression incomplete"
       (ParamExpectedNested _ _) => Left "incomplete application: second expression incomplete"
       (ParsedTerm x) => Right x

data RTTerm
  = RTVar Char
  | Closure Char RTTerm (List (Char, RTTerm))
  | RTAppl RTTerm RTTerm

Env : Type
Env = List (Char, RTTerm)

toRTTerm : Term -> RTTerm
toRTTerm (Var x) = RTVar x
toRTTerm (Func x y) = Closure x (toRTTerm y) []
toRTTerm (Appl x y) = RTAppl (toRTTerm x) (toRTTerm y)

mutual
  partial
  evalInEnv : Env -> RTTerm -> Either String RTTerm
  evalInEnv env (RTVar y) = maybe (Left $ strCons y " not found in env") Right $ lookup y env
  evalInEnv env clo@(Closure y z []) = Right $ Closure y z env
  evalInEnv env clo@(Closure y z (x :: xs)) = Right clo
  evalInEnv env (RTAppl f x) = do
    closurePlz <- evalInEnv env f
    case closurePlz of
        (Closure arg body env') => appl env arg body env' x
        _ => Left "SCREEEEEEEEEEEEEEEEEEW YOU!!!"

  partial
  appl : Env -> Char -> RTTerm -> Env -> RTTerm -> Either String RTTerm
  appl outerEnv arg body innerEnv paramExpr = do
    param <- evalInEnv outerEnv paramExpr
    let env = (arg, param) :: (innerEnv ++ outerEnv)
    evalInEnv env body

partial
eval : Term -> Either String RTTerm
eval = evalInEnv [] . toRTTerm

mutual
  partial
  showTerm : String -> (Char, RTTerm) -> String
  showTerm tab (c, term) =
    tab ++ singleton c ++ " is " ++ pretty' ("  " ++ tab) term

  partial
  showEnv : String -> Env -> String
  showEnv tab [] = ""
  showEnv tab xs@(_ :: _) =
    "\n" ++ tab ++ "where environemnt is:\n" ++ unlines (map (showTerm $ tab ++ "  ") xs)

  partial
  pretty' : String -> RTTerm -> String
  pretty' _ (RTVar x) = singleton x
  pretty' tab (Closure x y env) = "^" ++ singleton x ++ "." ++ pretty' tab y ++ showEnv tab env
  pretty' tab (RTAppl x y) = "(" ++ pretty' tab x ++ " " ++ pretty' tab y ++ ")"

partial
pretty : Either String RTTerm -> String
pretty (Left l) = l
pretty (Right r) = pretty' "  " r

partial
interp : String -> String
interp code = pretty $ ((parse . tokenize . unpack) code >>= eval)

