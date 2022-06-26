{-
    Università di Bologna
    Corso di laurea in Informatica
    93283 - Logica per l'informatica

    Stefano Volpe #969766
    21/10/2020

    Permutazioni.hs
-}

module Permutazioni (
    permutazioni,
    inserimenti,
    mappa,
    unione
) where

import Parti

permutazioni :: [a] -> [[a]] -- Problema 2
inserimenti :: a -> [a] -> [[a]] -- Problema 2.1
mappa :: (a -> b) -> [a] -> [b] -- Problema 2.2
unione :: [[a]] -> [a] -- Problema 2.3

{-
    Problema 2: data una lista l calcolare tutte le permutazioni di l
    rappresentate come lista di liste.
    
    Es. permutazioni (1 : 2 : 3 : []) =
        (1 : 2 : 3 : []) :
        (1 : 3 : 2 : []) :
        (2 : 1 : 3 : []) :
        (2 : 3 : 2 : []) :
        (3 : 1 : 2 : []) :
        (3 : 2 : 1 : []) : []
    Soluzione: permutazioni l
-}

permutazioni [] = [] : []
permutazioni (x : l) = unione (mappa (inserimenti x) (permutazioni l))

{-
    Problema 2.1: dati un elemento x e una lista l, restituire la lista di
    tutti i possibili modi di inserire x in l

    Es. inserimenti 1 (2 : 3 : []) =
        (1 : 2 : 3 : []) :
        (2 : 1 : 3 : []) :
        (2 : 3 : 1 : []) : []
    Soluzione: inserimenti x l
-}

inserimenti x [] = (x : []) : []
inserimenti x (y : l) = (x : y : l) : (premetti y (inserimenti x l))

{-
    Problema 2.2: data una lista l di elementi x1 : ... : xn : [] e una funzione
    f restituire la lista f x1 : ... (f xn) : []
    
    Es. mappa double (1 : 2 : 3 : []) = 2 : 4 : 6 : []
    Soluzione mappa f l
-}

mappa _ [] = []
mappa f (x : l) = f x : (mappa f l)

{-
    Problema 2.3: data una lista di liste ll pensata come insieme di insiemi,
    calcolare la lista che rappresenta l'unione di tutti gli elementi di ll.

    Es. unione ((1 : 2 : []) : (3 : 4 : []) : []) = 1 : 2 : 3 : 4 : []
    Soluzione unione ll
-}

unione [] = []
unione (l : ll) = unioneBinaria l (unione ll)