{-
    Università di Bologna
    Corso di laurea in Informatica
    93283 - Logica per l'informatica

    Stefano Volpe #969766
    28/10/2020

    Concatenazione.hs
-}

module Lunghezza(
    concatenazione,
    lunghezza
) where

concatenazione :: [a] -> [a] -> [a] -- Problema 11
lunghezza :: Num p => [a] -> p -- Problema 11.1

{-
    Problema 11: date due liste l1 ed l2, concatenarle.

    Es. concatenazione (1 : 2 : 4 : []) (1 : 3 : []) = 1 : 2 : 4 : 1 : 3 : []
    Soluzione: concatenazione l1 l2
-}

concatenazione [] l2 = l2
concatenazione (x : l) l2 = x : (concatenazione l l2)

{-
    Problema 11.1: data una lista l, restituirne la lunghezza.
    
    Es. lunghezza (1 : 2 : []) = 2
    Soluzione lunghezza l
-}

lunghezza [] = 0
lunghezza (_ : l) = 1 + lunghezza l

{-
    Th: ∀ l1 ∀ l2 (lunghezza(concatenazione l1 l2) = lunghezza l1 + lunghezza l2)
    Dim:
        Procedo per induzione strutturale su l1 per dimostrare ∀ l2 lunghezza(concatenazione l1 l2) = lunghezza l1 + lunghezza l2).
        - caso []:
            Devo dimostrare ∀ l2 lunghezza(concatenazione [] l2) = lunghezza [] + lunghezza l2, ovvero
            ∀ l2 lunghezza l2 = 0 + lunghezza l2
            Sia l2 una lista. Devo dimostrare lunghezza l2 = 0 + lunghezza l2.
                Ovvio per le proprietà della somma.
        - caso x : l:
            Ipotesi induttiva su l: ∀ l2 lunghezza(concatenazione l l2 = lunghezza l + lunghezza l2 (II)
            Devo dimostrare ∀ l2 lunghezza(concatenazione (x : l) l2) = lunghezza (x : l) + lunghezza l2, ovvero
            ∀ l2 lunghezza(x : concatenazione (l l2)) = 1 + lunghezza l + lunghezza l2, ovvero
            ∀ l2 1 + lunghezza(concatenazione (l l2)) = 1 + lunghezza l + lunghezza l2
                Sia l2 una lista. Devo dimostrare 1 + lunghezza(concatenazione (l l2)) = 1 + lunghezza l + lunghezza l2.
                Per II, ciò è equivalente a dimostrare 1 + lunghezza l + lunghezza l2 = 1 + lunghezza l + lunghezza l2.
                    Ovvio.
        Come volevasi dimostrare.
-}