{-
    Università di Bologna
    Corso di laurea in Informatica
    93283 - Logica per l'informatica

    Stefano Volpe #969766
    27/10/2020

    Laboratorio3valutato.hs
-}

{-
    Esercizio 1
-}

data E = Var String | Num Int | Plus E E | Times E E deriving Show

-- Sostituisce in s il valore di s secondo l, o 0 se s manca in l
sost _ [] = 0
sost s ((v, n) : l) = if s == v then n else sost s l

-- Valuta l'espressione
eval (Var s) l = sost s l
eval (Num i) _ = i
eval (Plus e f) l = (eval e l) + (eval f l)
eval (Times e f) l = (eval e l) * (eval f l)

{-
    Esercizio 2
-}

-- Controlla se l2 sia un prefisso di l1
prefisso [] [] = True
prefisso (_ : _) [] = True
prefisso [] (_ : _) = False
prefisso (x : l) (y : l2) = y == x && prefisso l l2

-- Assunto che l2 sia un prefisso di l1, lo rimuove
rimuovi_prefisso [] (_ : _) = []
rimuovi_prefisso (x : l) [] = x : l
rimuovi_prefisso [] [] = []
rimuovi_prefisso (_ : l) (_ : l2) = rimuovi_prefisso l l2

-- Rimuove una eventuale prima occorrenza di l2 da l1
m [] _ = []
m (x : l1) l2 = if prefisso (x : l1) l2 then
                      rimuovi_prefisso (x : l1) l2 else
                      x : (m l1 l2)

{-
    Esercizio 3
-}

-- Restituisce il numero di volte che a occorre in l 
occorrenze _ [] = 0
occorrenze a (x : l) = (if a == x then 1 else 0) + (occorrenze a l)

-- Date due liste l1 e l2, g controlla se almeno un numero compaia esattamente due volte fra l1 e x : l2
g _ [] = False
g l1 (x : l2) = (occorrenze x l1) + (occorrenze x (x : l2)) == 2 || g ( x : l1) l2

-- Controlla se almeno un numero compaia esattamente due volte in l
f l = g [] l