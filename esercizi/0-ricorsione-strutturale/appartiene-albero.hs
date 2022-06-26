{-
    Università di Bologna
    Corso di laurea in Informatica
    93283 - Logica per l'informatica

    Stefano Volpe #969766
    27/10/2020

    AppartieneAlbero.hs
-}

module AppartieneAlbero(
    appartieneAlbero
) where

data T = Leaf Int | Node T T deriving Show

appartieneAlbero :: Int -> T -> Bool -- Problema 9

{-
    Problema 9: dato un numero X e un albero T, resituire "vero" se e solo se
    X occorre come foglia in T, e "falso" altrimenti.

    Es. appartieneAlbero 2 (Node (Node (Leaf 1) (Leaf 3)) (Leaf 4)) = False
        appartieneAlbero 3 (Node (Node (Leaf 1) (Leaf 3)) (Leaf 4)) = True
    Soluzione: appartieneAlbero X T
-}

appartieneAlbero x (Leaf y) = x == y
appartieneAlbero x (Node y z) = appartieneAlbero x y || appartieneAlbero x z