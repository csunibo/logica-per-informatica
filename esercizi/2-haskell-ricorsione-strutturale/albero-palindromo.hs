{-
    Università di Bologna
    Corso di laurea in Informatica
    93283 - Logica per l'informatica

    Stefano Volpe #969766
    27/10/2020

    AlberoPalindromo.hs
-}

module AlberoPalindromo(
    alberoPalindromo,
    sequenza,
    palindromo,
    inversione
) where

import Parti(unioneBinaria)
import Crescenza (T(..))

alberoPalindromo :: T -> Bool -- Problema 10
sequenza :: T -> [Int] -- Problema 10.1
palindromo :: Eq a => [a] -> Bool -- Problema 10.2
inversione :: [a] -> [a] -- Problema 10.2.1

{-
    Problema 10: dato un albero T restituire "vero" se e solo se leggendo da
    destra verso sinistra o da sinistra verso destra le foglie dell'albero si
    ottiene la stessa lista di numeri.

    Es. alberoPalindromo (Node (Leaf 1) (Node (Leaf 2) (Leaf 1))) = True
        alberoPalindromo (Node (Node (Leaf 1) (Leaf 2)) (Node (Leaf 1) (Leaf 2))) = False
    Soluzione: alberoPalindromo T
-}

alberoPalindromo x = palindromo (sequenza x)

{-
    Problema 10.1: dato un albero T restituire la sua conversione in lista.

    Es. sequenza (Node (Node (Leaf 1) (Leaf 2)) (Node (Leaf 1) (Leaf 2))) =
        1 : 2 : 1 : 2 : []
    Soluzione: sequenza T
-}

sequenza (Leaf x) = x : []
sequenza (Node x y) = unioneBinaria (sequenza x) (sequenza y)

{-
    Problema 10.2: data una sequenza l, controllare se questa sia un
    palindromo o meno.
    
    Es. palindromo (1 : 5 : 2 : 5 : 2 : []) = True
    Soluzione: palindromo l
-}

palindromo x = x == inversione x

{-
    Problema 10.2.1: data una sequenza l, computarne l'inversione.
    
    Es. inversione (1 : 2 : 9 : 2 : []) = 2 : 9 : 2 : 1 : []
    Soluzione: inversione l
-}

inversione [] = []
inversione (x : l) = unioneBinaria (inversione l) (x : [])