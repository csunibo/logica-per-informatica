{-
    Università di Bologna
    Corso di laurea in Informatica
    93283 - Logica per l'informatica

    Stefano Volpe #969766
    10/11/2020

    Intersezione.hs
-}


module Intersezione
    intersezione
) where

import Parti(intersezioneBinaria)

{-
    Problema 15: scrivere una funzione che, data in input una lista l di liste
    di numeri, restituisca la lista o di tutti e soli i numeri che occorrono
    in tutte le liste in l.

    Es. o (1 : 2 : 3 : 4 : 5 : []) :
          (2 : 3 : 4 : 5 : []) :
          (1 : 2 : 3 : 4 : []) = 2 : 3 : 4 : []
    Soluzione: o l
-}

intersezione [] = []
intersezione (l : ll) = intersezioneBinaria l (o ll)