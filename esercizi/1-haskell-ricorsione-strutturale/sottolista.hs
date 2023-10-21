{-
    Università di Bologna
    Corso di laurea in Informatica
    93283 - Logica per l'informatica

    Stefano Volpe #969766
    22/10/2020

    Sottolista.hs
-}

module Sottolista (
    sottolista,
    prefisso
) where

sottolista :: Eq a => [a] -> [a] -> Bool -- Problema 4
prefisso :: Eq a => [a] -> [a] -> Bool -- Problema 4.1

{-
    Problema 4: date due liste l1 e l2 decidere se l2 sia o meno una sottolista
    di l1.

    Es. sottolista (1 : 2 : 3 : 4 : []) : (2 : 3 : []) = True
    Es. sottolista (1 : 2 : 3 : 4 : []) : (1 : 3 : []) = False
    Soluzione: sottolista l1 l2
-}

sottolista [] l2 = l2 == []
sottolista (x : l) l2 = sottolista l l2 || prefisso (x : l) l2

{-
    Problema 4.1: date due liste l1 e l2 decidere se l2 sia o meno un prefisso
    di l1.

    Es. prefisso (1 : 2 : 3 : 4 : []) (1 : 2 : []) = True
    Es. prefisso (1 : 2 : 3 : 4 : []) (2 : 3 : []) = False
    Soluzione prefisso l1 l2
-}

-- prefisso [] [] = True
prefisso [] (_ : _) = False
-- prefisso (_ : _) [] = True
prefisso _ [] = True
prefisso (x : l1) (y : l2) = x == y && prefisso l1 l2