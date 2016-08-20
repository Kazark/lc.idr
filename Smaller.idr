module Smaller

%default total
%access public export

data Smaller : List a -> List b -> Type where
  SmallerZ : Smaller [] (x :: xs)
  SmallerS1 : Smaller s b -> Smaller s (y :: b)
  SmallerS2 : Smaller s b -> Smaller (x :: s) (y :: b)

peelOffProof : (bigL : List a) -> {auto prf : NonEmpty bigL} -> Smaller (tail bigL) bigL
peelOffProof [] {prf=IsNonEmpty} impossible
peelOffProof (_ :: []) = SmallerZ
peelOffProof (_ :: xs@(_ :: _)) = SmallerS2 $ peelOffProof xs

peelOff : (bigL : List a) -> {auto prf : NonEmpty bigL} -> (smallL : List a ** Smaller smallL bigL)
peelOff [] {prf=IsNonEmpty} impossible
peelOff (_ :: []) = ([] ** SmallerZ)
peelOff bigL@(_ :: xs@(_ :: _)) = (xs ** SmallerS2 $ peelOffProof xs)

(::) : {bigL : List b} -> (x : b) -> Smaller smallL bigL -> Smaller smallL (x :: bigL)
(::) _ smaller = SmallerS1 smaller

(++) : {bigL : List b} -> (xs : List b) -> Smaller smallL bigL -> Smaller smallL (xs ++ bigL)
(++) [] smaller = smaller
(++) (_ :: xs) smaller = SmallerS1 (xs ++ smaller)

consToType : {bigL : List b} -> (x : b) ->
             (smallL : List a ** Smaller smallL bigL) ->
             (smallL : List a ** Smaller smallL (x :: bigL))
consToType x (smallL ** pf) = (smallL ** SmallerS1 pf)

appendToType : {bigL : List b} -> (xs : List b) ->
               (smallL : List a ** Smaller smallL bigL) ->
               (smallL : List a ** Smaller smallL (xs ++ bigL))
appendToType [] smaller = smaller
appendToType xs@(_ :: _) (smallL ** pf) = (smallL ** xs ++ pf)

(+) : Smaller l1 l2 -> Smaller l2 l3 -> Smaller l1 l3
(+) SmallerZ (SmallerS1 _) = SmallerZ
(+) SmallerZ (SmallerS2 _) = SmallerZ
(+) (SmallerS1 x) (SmallerS1 z) = SmallerS1 (x + z)
(+) (SmallerS1 x) (SmallerS2 z) = ?asdf1_2
(+) (SmallerS2 z) (SmallerS1 x) = ?asdf1_4
(+) (SmallerS2 z) (SmallerS2 x) = ?asdf1_5
