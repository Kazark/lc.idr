module TotalityOrWhat

import Data.Vect

%default total

data Instruction = Jump Nat | Return Char | Error

parse : List Char -> Instruction
parse ('j' :: '1' :: _) = Jump 1
parse ('j' :: '2' :: _) = Jump 2
parse ('j' :: '3' :: _) = Jump 3
parse ('r' :: x :: _) = Return x
parse _ = Error

parseDriver : String -> Maybe Char
parseDriver = parseDriver' (Jump 1) . unpack where
  parseDriver' : Instruction -> List Char -> Maybe Char
  parseDriver' (Jump k) [] = Nothing
  parseDriver' (Jump Z) _ = Nothing
  parseDriver' (Jump (S Z)) (x :: xs) = parseDriver' (parse xs) xs
  parseDriver' (Jump (S k)) xs@(_ :: _) = parseDriver' (Jump k) xs
  parseDriver' (Return x) _ = Just x
  parseDriver' Error _ = Nothing
