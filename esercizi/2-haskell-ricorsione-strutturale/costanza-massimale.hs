{-
    Università di Bologna
    Corso di laurea in Informatica
    93283 - Logica per l'informatica

    Stefano Volpe #969766
    22/10/2020

    CostanzaMassimale.hs
-}

module CostanzaMassimale (
    costanzaMassimale,
    costanzaPrefisso
) where

costanzaMassimale :: (Num p, Ord p, Eq t) => [t] -> p -- Problema 5
costanzaPrefisso :: (Num p, Eq t) => t -> [t] -> p -- Problema 5.1

{-
    Problema 5: data una lista l calcolare la lunghezza della sottolista di l
    composta da elementi tutti uguali di lunghezza massimale.

    Es. costanzaMassimale (1 : 1 : 2 : 2 : 2 : 3 : []) = 3
    Soluzione: costanzaMassimale l
-}

costanzaMassimale [] = 0
costanzaMassimale (x : l) = max (costanzaMassimale l) (1 + (costanzaPrefisso x l))

{-
    Problema 5.1: dato un x e una lista l,
    calcolare la lunghezza del prefisso
    massimale di l formato da sole x

    Es. costanzaPrefisso (1 : 1 : 2 : 2 : 2 : 3 : []) = 2
    Soluzione costanzaPrefisso l
-}

costanzaPrefisso _ [] = 0
costanzaPrefisso x (y : l) = if x == y then 1 + (costanzaPrefisso x l) else 0