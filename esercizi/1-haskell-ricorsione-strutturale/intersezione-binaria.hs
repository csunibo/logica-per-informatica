{-
    Università di Bologna
    Corso di laurea in Informatica
    93283 - Logica per l'informatica

    Stefano Volpe #969766
    27/10/2020

    IntersezioneBinaria.hs
-}

module IntersezioneBinaria(
    intersezioneBinaria,
    appartiene
) where

intersezioneBinaria :: Eq a => [a] -> [a] -> [a] -- Problema 7
appartiene :: Eq t => t -> [t] -> Bool -- Problema 7.1

{-
    Problema 7: date due liste l1 e l2, restituire la lista degli elementi
    comuni a l1 e l2.

    Es. intersezioneBinaria (1 : 3 : 4 : 6 : []) (3 : 6 : 2 : 5 : 1 : []) =
        (1 : 3 : 6 : [])
    Soluzione: intersezioneBinaria l1 l2
-}

intersezioneBinaria [] _ = []
intersezioneBinaria (x : l1) l2 = if appartiene x l2 then
                           x : (intersezioneBinaria l1 l2) else
                           intersezioneBinaria l1 l2

{-
    Problema 7.1: dato x ed una lista l, restituire "vero" se e solo se x
                  appartiene ad l

    Es. appartiene 6 (3 : 6 : 2 : 5 : 1 : []) = True
    Soluzione: appartiene x l
-}

appartiene _ [] = False
appartiene x (y : l) = x == y || (appartiene x l)