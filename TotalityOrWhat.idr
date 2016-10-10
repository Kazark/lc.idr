module TotalityOrWhat

import Data.Vect

%default total

data Instruction = Jump Nat | Return Char | Error

total parseDriver : String -> Maybe Char
parseDriver = parseDriver' . unpack where
  parseDriver' : List Char -> Maybe Char
  parseDriver' ('j' :: '1' :: xs) = parseDriver' ('1' :: xs)
  parseDriver' ('j' :: '2' :: xs) = parseDriver' xs
  parseDriver' ('j' :: '3' :: _ :: xs) = parseDriver' xs
  parseDriver' ('r' :: x :: _) = Just x
  parseDriver' _ = Nothing
