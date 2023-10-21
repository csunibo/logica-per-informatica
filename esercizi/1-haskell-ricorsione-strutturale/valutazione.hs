{-
    Università di Bologna
    Corso di laurea in Informatica
    93283 - Logica per l'informatica

    Stefano Volpe #969766
    27/10/2020

    Valutazione.hs
-}

module Valutazione(
    valutazione
) where

data E = Num Int | Plus E E | Times E E deriving Show

valutazione :: E -> Int -- Problema 10

{-
    Problema 10: data un'espressione E (una connotazione), calcolare il
    risultato dell'espressione (la sua denotazione interpretando Plus com + e
    Times come * sull'insieme dei numeri naturali).

    Es. valutazione (Times (Plus (Num 2) (Num 3)) (Num 2)) = 10
    Soluzione: valutazione E
-}

valutazione (Num i) = i
valutazione (Plus e f) = valutazione(e) + valutazione(f)
valutazione (Times e f) = valutazione(e) * valutazione(f)