-- Author: Matteo Lombardi

-- TreeL ::= Node TreeL TreeL ! Leaf Int

data TreeL = Node TreeL TreeL | Leaf Int deriving (Show)

-- Problema 3: dato un TreeL, restituire il valore della foglia più a sx
-- Funzione: sxLeaf t
-- Esempio: sxLeaf (Node (Node (Leaf 1) (Leaf 3)) (Node (Node (Leaf 5) (Leaf 7)) = 7

sxLeaf (Leaf n) = n
sxLeaf (Node t1 t2) = sxLeaf t2

-- Problema 2: dato un TreeL, restituire il valore della foglia più a dx
-- Funzione: dxLeaf t
-- Esempio: dxLeaf (Node (Node (Leaf 1) (Leaf 3)) (Node (Node (Leaf 5) (Leaf 7)) = 7

dxLeaf (Leaf n) = n
dxLeaf (Node t1 t2) = dxLeaf t2

-- Problema 1: dato un TreeL, restituire True sse la sequenza di foglie da sx a dx è crescente in senso stretto
-- Funzione: incr t
-- Esempio: incr (Node (Node (Leaf 1) (Leaf 3)) (Node (Node (Leaf 5) (Leaf 7)) (Node (Leaf 8) (Leaf 9)))) = True

incr (Leaf n) = True
incr (Node t1 t2) = incr t1 && incr t2 && (dxLeaf t1) < (sxLeaf t2)

--------------------------------------------

-- TreeL ::= Empty | TreeL Node TreeL

data TreeB = Empty | NodeB Int TreeB TreeB deriving (Show)

-- Problema 1
