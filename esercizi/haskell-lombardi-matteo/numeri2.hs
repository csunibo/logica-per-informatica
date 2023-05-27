-- Author: Matteo Lombardi

data Nat = O | S Nat deriving (Show)

-- Problema: dati due naturali, sommarli
-- Soluzione: plus m n
-- Esempio: plus (S (S (S O))) (S (S O)) = S (S (S (S (S O))))

plus m O = m
plus m (S n) = S (plus m n)

-- Problema: dati due naturali, moltiplicarli
-- Soluzione: mult m n
-- Esempio: mult (S (S O)) (S (S (S O))) = S (S (S (S (S (S O))))

mult m O = O
mult m (S n) = plus m (mult m n)