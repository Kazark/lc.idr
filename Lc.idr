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

partial
parseSingle : List Token -> Either String (Term, List Token)
parseSingle [] = Left "empty list"
parseSingle (LParen :: xs) = do
  (first, secondToks) <- parseSingle xs
  (second, rest) <- parseSingle secondToks
  case rest of
    RParen :: blah => Right (Appl first second, blah)
    _ => Left "Failed to find closing parenthesis"
parseSingle (RParen :: xs) = Left "encountered unexpected opening parenthesis"
parseSingle (Dot :: xs) = Left "encountered unexpected dot"
parseSingle (Lambda :: Alpha argName :: Dot :: xs) =
  map (\(body, rest) => (Func argName body, rest)) $ parseSingle xs
parseSingle ((Alpha x) :: xs) = Right (Var x, xs)
parseSingle _ = Left "Pattern match failed"

partial
parse : List Token -> Either String Term
parse = map fst . parseSingle

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

