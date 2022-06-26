{-
    Università di Bologna
    Corso di laurea in Informatica
    93283 - Logica per l'informatica

    Stefano Volpe #969766
    27/10/2020

    Picchi.hs
-}

module Picchi(
    picchi
) where

picchi :: Ord a => [a] -> [a] -- Problema 8
nonMinoreDiTesta :: Ord a => a -> [a] -> Bool -- Problema 8.1

{-
    Problema 8: data una lista l di numeri, un picco di l è un numero che non
    occorre in l immediatamente prima di un numero più grande di lui.
    Restituire la lista di tutti i picchi di l.-
    
    Es. picchi (4 : 1 : 2 : 5 : 3 : 1 : 6 : []) = 4 : 5 : 3 : 6 : []
    Soluzione: picchi l
-}

picchi [] = []
picchi (x : l) = if nonMinoreDiTesta x l then x : picchi l else picchi l

{-
    Problema 8.1: dato un valore x e una lista di l, restituire "falso" se e
    solo se l ha una testa e quella testa è maggiore di x

    Es. picchi 5 (4 : []) = True
    Soluzione: nonMinoreDiTesta x l
-}

nonMinoreDiTesta _ [] = True
nonMinoreDiTesta x (y : _) = x >= y