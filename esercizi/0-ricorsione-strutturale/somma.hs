{-
    Università di Bologna
    Corso di laurea in Informatica
    93283 - Logica per l'informatica

    Stefano Volpe #969766
    28/10/2020

    Somma.hs
-}

module Somma(
    N,
    sommaSX,
    sommaDX
) where

data N = O | S N deriving Show -- rappresentazione "base 1"

sommaSX :: N -> N -> N -- Problema 14
sommaDX :: N -> N -> N

{-
    Problema 14: dati due naturali x ed y, computarne la somma.

    Es. S(O) + S(S(S(O))) = S(S(S(S(O))))
    Soluzione: x + y
-}

-- sommaSX = .+
sommaSX O y = y
sommaSX (S n) y = S (sommaSX n  y)

-- sommaDX = +.
sommaDX x O = x
sommaDX x (S n) = S (sommaDX x  n)

{-
    Lem: y = y + 0
    Dim:
        Devo dimostrare ∀ y y = y + 0.
        Procedo per induzione strutturale su y per dimostrare y = y + 0.
        - caso O:
            Devo dimostrare 0 = 0 + 0, ovvero 0 = 0.
                Ovvio.
        - caso S n:
            n = n + 0 (II).
            Devo dimostrare S n = S n + 0, ovvero S n = S(n + 0).
                Per II, mi riduco a dimostrare S n = S n.
                    Ovvio.
    Come volevasi dimostrare.

    Lem2: S (x + y) = x + S y.
    Dim:
        Devo dimostrare ∀ x ∀ y S (x + y) = x + S y.
        Procedo per induzione strutturale su x per dimostrare ∀ y S(x + y) = x + S y.
        - caso O:
            Devo dimostrare ∀ y S (0 + y) = 0 + S y, ovvero ∀ y S y = S y.
                Sia y un numero.
                Devo dimostrare S y = S y.
                    Ovvio.
        - caso S n:
            ∀ y S(n + y) = n + S y (II).
            Devo dimostrare ∀ y S (S n + y) = S n + S y, ovvero ∀ y S (S (n + y)) = S (n + S y),
                Sia y un numero.
                Devo dimostrare S( S( n + y)) = S ( n + S y).
                    Per II, mi riduco a dimostrare S(n + S y) = S (n + S y).
                        Ovvio.
    Come volevasi dimostrare.

    Th: x + y = y + x.
    Dim:
        Devo dimostrare ∀ x ∀ y x + y = y + x.
        Procedo per induzione strutturale su x per dimostrare ∀ y x + y = y + x.
        - caso O:
            Devo dimostrare ∀ y 0 + y = y + 0, ovvero ∀ y y = y + 0.
                Sia y un numero.
                Devo dimostrare che y = y + 0.
                    Ovvio per il lemma.
        - caso S n
            ∀ y n + y = y + n (II).
            Devo dimostrare ∀ y S n + y = y + S N, ovvero ∀ y S (n + y) = y + S n.
                Sia y un numero.
                Devo dimostrare S (n + y) = y + S n.
                    Per II, mi riduco a dimostrare S(y + n) = y + S n.
                        Ovvio per lemma 2.
-}

{-
    Lem: y = 0 +. y
    Dim:
        Devo dimostrare ∀ y y = 0 +. y.
        Procedo per induzione strutturale su y per dimostrare y = 0 +. y.
        - caso O:
            Devo dimostrare 0 = 0 +. 0, ovvero 0 = 0.
                Ovvio.
        - caso S n:
            n = 0 +. n (II).
            Devo dimostrare S n = 0 +. S n, ovvero S n = S(0 +. n).
                Per II, mi riduco a dimostrare S n = S n.
                    Ovvio.
    Come volevasi dimostrare.

    Lem: S(x +. y) = S x +. y
    Dim:
        [...]

    Teorema: x .+ y = x +.y
    Dim:
        Procedo per induzione strutturale su x per dimostrare ∀ y x .+ y = x +. y.
        - caso O: devo dimostrare ∀ y O .+ y = O +. y, ovvero ∀ y y = 0 +. y.
            Ovvio per lemma.
        - caso S n: devo dimostare ∀ y S n .+ y = S n +. y, ovvero
            ∀ y S(n .+ y) = S n +. y.
            ∀ y n .+ y = n +. y (II).
            Sia y un numero.
            Devo dimostrare S (n .+ y) = S n +. y.
            Per II, mi riduco a dimostrare S (n +. y) = S n +. y.
                Ovvio per lemma 2. 
-}