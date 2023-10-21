{-
    Università di Bologna
    Corso di laurea in Informatica
    93283 - Logica per l'informatica

    Stefano Volpe #969766
    21/10/2020

    Parti.hs
-}

module Parti (
    parti,
    unioneBinaria,
    premetti
) where

parti :: [a] -> [[a]] -- Problema 1 
unioneBinaria :: [a] -> [a] -> [a] -- Problema 1.1
premetti :: a -> [[a]] -> [[a]] -- Problema 1.2

{-
    Problema 1: data una lista l pensata come un insieme,
    calcolare l'insieme delle parti di l visto come lista di liste.
    
    Es. parti (1 : 2 : []) = [] : (1 : []) : (2 : []) : (1 : 2 : []) : []
    Soluzione: parti l
-}

parti [] = [] : []
parti (x : l) = unioneBinaria (parti l) (premetti x (parti l))

{-
    Problema 1.1: date due liste l1 e l2 pensate come insiemi, calcolare la
    lista che ne rappresenta l'unione.

    Es. unioneBinaria (1 : 2 : []) (3 : 4 : []) = 1 : 2 : 3 : 4 : []
    Soluzione: unioneBinaria l1 l2
-}

unioneBinaria [] l2 = l2
unioneBinaria (x : l) l2 = x : unioneBinaria l l2

{-
    Problema 1.2: dati un elemento x e una lista di liste ll, aggiungere x in
    testa a tutte le liste contenute in ll.

    Es. i 1 ((2 : 3 : []) : [] : []) = (1 : 2 : 3 : []) : (1 : []) : []
    Soluzione: premetti x ll
-}

premetti _ [] = []
premetti x (l : ll) = (x : l) : premetti x ll