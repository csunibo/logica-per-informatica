{-
    Università di Bologna
    Corso di laurea in Informatica
    93283 - Logica per l'informatica

    Stefano Volpe #969766
    28/10/2020

    Ennesimo.hs
-}

module Ennesimo(
    ennesimo
) where

ennesimo :: (Eq t, Num p, Num t) => t -> [p] -> p -- Problema 13

{-
    Problema 13: dato un naturale i e una lista l = x1 : ... : xn : [] tali che 0 < i <= n,
    restituire xi.

    Es. ennesimo 2 (3 : 11 : 5 : []) = 11
    Soluzione: ennesimo i l
-}

ennesimo _ [] = 0 -- violazione delle assunzioni
ennesimo i (x : l) = if i == 1 then x else ennesimo (i - 1) l

{-
    Th: ∀ l1 ∀ l2 ∀ i 1 <= i && i <= length l1 -> ennesimo i l1 = ennesimo i (concatenazione l1 l2)
    Dim:
        Procedo per induzione strutturale su l1 per dimostrare ∀ l2 ∀ i 1 <= i && i <= length l1 -> ennesimo i l1 = ennesimo 1 (concatenazione l1 l2).
        - caso []:
            Devo dimostrare ∀ l2 ∀ i 1 <= i && i <= length [] -> ennesimo i [] = ennesimo 1 (concatenazione [] l2), ovvero
            ∀ l2 ∀ i 1 <= i && i <= 0 -> 0 = ennesimo 1 l2.
                Siano l2 una lista e i un intero tale che 1 <= i (H1) e i <= 0 (H2).
                Devo dimostrare 0 = ennesimo 1 l2.
                    Per la proprietà transitiva di <=, H1 e H2, assurdo.
                    Quindi ennesimo 1 l2.
        - caso x : l:
            Ipotesi induttiva su l: ∀ l2 ∀ i 1 <= i && i <= length l -> ennesimo i l = ennesimo 1 (concatenazione l l2) (II).
            Devo dimostrare ∀ l2 ∀ i 1 <= i && i <= length (x : l) -> ennesimo i (x : l) = ennesimo 1 (concatenazione (x : l) l2), ovvero
            ∀ l2 ∀ i 1 <= i && i <= 1 + length l -> (if i == 1 then x else ennesimo (i - 1) l) = ennesimo 1 (x : concatenazione (l l2)), ovvero
            ∀ l2 ∀ i 1 <= i && i <= 1 + length l -> (if i == 1 then x else ennesimo (i - 1) l) = (if i == 1 then x else ennesimo (i - 1) (concatenazione l l2)).
                Siano l2 una lista e i un intero tale che 1 <= i (H1) e i <= 1 + length l (H2).
                Devo dimostrare (if i == 1 then x else ennesimo (i - 1) l) = (if i == 1 then x else ennesimo (i - 1) (concatenazione l l2)).
                    Per la proprietà dei numeri naturali, i == 1 o non (i == 1).
                    - caso i == 1: devo dimostrare (if True then x else ennesimo (i - 1) l) = (if True then x else ennesimo (i - 1) (concatenazione l l2)), ovvero x = x.
                        Ovvio.
                    - caso non (i == 1) (H3): devo dimostrare (if False then x else ennesimo (i - 1) l) = (if False then x else ennesimo (i - 1) (concatenazione l l2)), ovvero
                    ennesimo (i - 1) l = ennesimo (i - 1) (concatenazione l l2).
                        Da H1 e H3, si ha 1 <= i - 1 (H4).
                        Da H2 ho i - 1 <= length l (H5).
                        Da H4, H5 e II ho ennesimo (i - 1) l = ennesimo (i - 1) (concatenazione l l2).
        Come volevasi dimostrare.
-}

{-
    Th: ∀ l1 ∀ l2 ∀ i 1 <= i && i <= length l2 -> ennesimo i l2 = ennesimo (lunghezza l1 + i) (concatenazione l1 l2)
    Dim:
        Procedo per induzione strutturale su l1 per dimostrare ∀ l2 ∀ i 1 <= i && i <= length l2 -> ennesimo i l2 = ennesimo (lunghezza l1 + i) (concatenazione l1 l2).
        - caso []:
            Devo dimostrare ∀ l2 ∀ i 1 <= i && i <= length l2 -> ennesimo i l2 = ennesimo (lunghezza [] + i) (concatenazione [] l2), ovvero
            ∀ l2 ∀ i 1 <= i && i <= length l2 -> ennesimo i l2 = ennesimo (0 + i) l2
                Ovvio per le proprietà della somma.
        - caso x : l:
            Ipotesi induttiva su l: ∀ l2 ∀ i 1 <= i && i <= length l2 -> ennesimo i l2 = ennesimo (lunghezza l + i) (concatenazione l l2) (II).
            Devo dimostrare ∀ l2 ∀ i 1 <= i && i <= length l2 -> ennesimo i l2 = ennesimo (lunghezza (x : l) + i) (concatenazione (x : l) l2), ovvero
            ∀ l2 ∀ i 1 <= i && i <= length l2 -> ennesimo i l2 = ennesimo (1 + lunghezza l + i) (x : (concatenazione l l2)), ovvero
            ∀ l2 ∀ i 1 <= i && i <= length l2 -> ennesimo i l2 = (if 1 + lunghezza l + i == 1 then x else ennesimo (1 + length l + i - 1) (concatenazione l l2)).
                Siano l2 una lista e i un intero tale che 1 <= i (H1) e i <= lunghezza l2 (H2).
                Devo dimostrare ennesimo i l2 = (if 1 + lunghezza l + i == 1 then x else ennesimo (1 + length l + i - 1) (concatenazione l l2)).
                - caso 1 + lunghezza l + i == 1 (H3): devo dimostrare ennesimo i l2 = x
                    Da H3, i == -lunghezza l.
                    Quindi, da H1 e dal lemma (mancante!) per cui v lunghezza ∀ l l > 0.
                - caso non (1 + lunghezza l + i == 1) (H3): devo dimostrare ennesimo i l2 = ennesimo (1 + lunghezza l + i - 1) (concatenazione l l2).
                    Per le proprietà dell'aritmetica, posso ridurmi a dimostare ennesimo i l2 = ennesimo (lunghezza l + i) (concatenazione l l2).
                        Ovvio per II, H1, H2.
    Come volevasi dimostrare.
-}