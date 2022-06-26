{-
    Università di Bologna
    Corso di laurea in Informatica
    93283 - Logica per l'informatica

    Stefano Volpe #969766
    28/10/2020

    Appartiene.hs
-}

module Appartiene(
    appartiene
) where

appartiene :: Eq t => t -> [t] -> Bool -- Problema 12

{-
    Problema 12: dato un elemento x e una lista l, controllare se x occorra
    almeno una volta in l.

    Es. appartiene 7 (2 : 3 : 8 : 7 : 7 : 0 : 7 : 1 : []) = True
    Soluzione: appartiene x l
-}

appartiene _ [] = False
appartiene x (y : l) = x == y || appartiene x l

{-
    Th: ∀ l1 ∀ l2 ∀x appartiene x (concatenazione l1 l2) = appartiene x l1 || appartiene x l2
    Dim:
        Procedo per induzione strutturale su l1 per dimostrare ∀ l2 ∀x appartiene x (concatenazione l1 l2) = appartiene x l1 || appartiene x l2.
        - caso []:
            Devo dimostrare ∀ l2 ∀x appartiene x (concatenazione [] l2) = appartiene x [] || appartiene x l2, ovvero
            ∀ l2 ∀x appartiene x l2 = False || appartiene x l2.
                Ovvio.
        - caso y : l:
            Ipotesi induttiva su l: ∀ l2 ∀ x appartiene x (concatenazione l l2) = appartiene x l || appartiene x l2 (II).
            Devo dimostrare ∀ l2 ∀ x appartiene x (concatenazione (y : l) l2) = appartiene x (y : l) || appartiene x l2, ovvero
            ∀ l2 ∀ x appartiene x (y : concatenazione l l2) = x == y || appartiene x l || appartiene x l2, ovvero
            ∀ l2 ∀ x x == y || appartiene x (concatenazione l l2) = x == y || appartiene x l || appartiene x l2.
                Siano l2 una lista e x un numero.
                Devo dimostrare x == y || appartiene x (concatenazione l l2) = x == y || appartiene x l || appartiene x l2.
                    Ovvio per II e per le proprietà della disgiunzione inclusiva.
        Come volevasi dimostrare.
-}