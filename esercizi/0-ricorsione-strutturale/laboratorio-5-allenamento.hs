{-
    Università di Bologna
    Corso di laurea in Informatica
    93283 - Logica per l'informatica

    Stefano Volpe #969766
    10/11/2020

    Laboratorio5allenamento.hs
-}

{-
    Esercizio 2
-}

-- Stabilisce se x appartenga o meno a l
appartiene _ [] = False
appartiene x (y : l) = x == y || appartiene x l

-- Restituisce l'intersezione binaria fra l1 e l2
intersezioneBinaria [] _ = []
intersezioneBinaria (x : l) m = if  appartiene x m then x : intersezione l m else intersezioneBinaria l m

-- Restituisce l'intersezione di tutte le liste della lista di liste
o [] = []
o (l : ll) = intersezioneBinaria l (o ll)