{-
    Università di Bologna
    Corso di laurea in Informatica
    93283 - Logica per l'informatica

    Stefano Volpe #969766
    21/10/2020

    Crescenza.hs
-}

module Crescenza (
    T(..),
    crescente,
    destra,
    sinistra
) where

data T = Leaf Int | Node T T deriving Show

crescente :: T -> Bool -- Problema 3
sinistra :: T -> Int -- Problema 3.1
destra :: T -> Int -- Problema 3.2

{-
    Problema 3: dato un albero a, restituire "vero" se e solo se leggendo le
    foglie da sinistra a destra si ottiene una successione crescente.

    Es. crescente (Node (Node (Int 2) (Int 3)) (Int 4)) = True
    Soluzione: crescente a
-}

crescente (Leaf _) = True
crescente (Node a1 a2) = crescente a1 &&
                         destra a1 <= sinistra a2 &&
                         crescente a2

{-
    Problema 3.1: dato un albero a, restituire la sua foglia più a sinistra.

    Es. sinistra Node (Node (Int 2) (Int 1)) (Int 6)) = 2
    Soluzione: sinistra a
-}

sinistra (Leaf x) = x
sinistra (Node a _) = sinistra(a)

{-
    Problema 3.2: dato un albero a, restituire la sua foglia più a destra.

    Es. destra Node (Node (Int 2) (Int 1)) (Int 6)) = 6
    Soluzione: destra a
-}

destra (Leaf x) = x
destra (Node _ a) = destra(a)