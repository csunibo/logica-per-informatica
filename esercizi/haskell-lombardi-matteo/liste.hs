-- -- Author: Matteo Lombardi

-- -- list A ::= [] | A : list A

-- -- Data una lista, restituisce la somma dei suoi elementi
list_sum [] = 0
list_sum (h : t) = h + (list_sum t)

---------------------------------------------------

-- -- Massimo degli elementi in una lista
list_max [] = 0
list_max (h : t) = if (list_max t > h) then (list_max t) else h

-- -- Problema 5: dato un elemento e una lista di liste, restituire una lista di tutte le liste della lista in input aventi in testa l'elemento dato in input
-- -- Funzione: insert_head_in_list_list h ll
-- -- Esempio: insert_head_in_list_list 1 ((2 t: 3 : []) : (4 : 2 : []) : []) =
-- -- ((1 : 2 : 3 : []) : (1 : 4 : 2 : []) : [])

insert_head_in_list_list h [] = []
insert_head_in_list_list h (l : ll) = (h : l) : (insert_head_in_list_list h ll)

-- Problema 4: date due liste, concatenarle
-- Funzione: concatenate l1 l2
-- Esempio: concatenate (1 : 3 : 2 : []) (4 : 2 : 5 : []) =
-- 1 : 3 : 2 : 4 : 2 : 5 : []

concatenate [] l2 = l2
concatenate (h : t) l2 = h : (concatenate t l2)

-- Problema 3: dati un elemento e una lista, restituire una lista di liste nelle quali l'elemento è stato inserito in tutte le posizioni possibili
-- Funzione: insert_everywhere_in_list x l
-- Esempio: insert_everywhere_in_list 1 (2 : 3 : []) =
-- (1 : 2 : 3 : []) : (2 : 1 : 3 : []) : (2 : 3 : 1 : []) : []

insert_everywhere_in_list x [] = (x : []) : []
insert_everywhere_in_list x (h : t) =
  (x : h : t) : (insert_head_in_list_list h (insert_everywhere_in_list x t))

-- Problema 2: dato un elemento e una lista di liste, restituire una lista di liste ottenuta da quella in input inserendo in ognuna delle liste in input l'elemento in tutte le posizioni possibili
-- Funzione: insert_everywhere_in_list_list x ll
-- Esempio: insert_everywhere_in_list_list 1 ((2 : 3 : []) : (3 : 2 : []) : []) =
-- (1 : 2 : 3 : []) : (2 : 1 : 3 : []) : (2 : 3 : 1 : []) :
-- (1 : 3 : 2 : []) : (3 : 1 : 2 : []) : (3 : 2 : 1 : []) : []

insert_everywhere_in_list_list x [] = []
insert_everywhere_in_list_list x (l : ll) =
  concatenate
    (insert_everywhere_in_list x l)
    (insert_everywhere_in_list_list x ll)

-- Problema 1: data una lista, calcolare l'insieme (lista di liste) di tutte le permutazioni della lista in input
-- Funzione: permut l
-- Esempio: permut (1 : 2 : 3 : []) =
-- (1 : 2 : 3 : []) : (2 : 1 : 3 : []) : (2 : 3 : 1 : []) :
-- (1 : 3 : 2 : []) : (3 : 1 : 2 : []) : (3 : 2 : 1 : []) : []

permut [] = [] : []
permut (h : t) = insert_everywhere_in_list_list h (permut t)

----------------------------------------------------

-- Problema 3: data una sequenza di numeri, restituirne la prima sottosequenza di numeri crescenti
-- Funzione: first_growing x l
-- Esempio: first_growing 2 (3 : 4 : 1 : 5 : 7 : 8 : 2 : []) = 2 : 3 : 4 : []

first_growing x [] = x : []
first_growing x (h : t) =
  if (x < h)
    then (x : (first_growing h t))
    else x : []

-- Problema 2: data una lista, restituirne la lunghezza
-- Funzione: len l
-- Esempio: len (3 : 2 : 7 : 1 : []) = 4

len [] = 0
len (h : t) = 1 + len t

-- Problema 1: data una sequenza di numeri, trovare la sottosequenza di numeri crescenti di lunghezza massima
-- Funzione: growing l
-- Esempio: growing (3 : 4 : 1 : 5 : 7 : 2 : 2 : []) = 1 : 5 : 7 : []

growing [] = []
growing (h : t) =
  if len (first_growing h t) > len (growing t)
    then (first_growing h t)
    else growing t

----------------------------------------------------

-- Problema 4: data una coppia (x, y), restituirne il secondo elemento
-- Funzione: second (x, y)
-- Esempio: second (2, 3) = 2

second (x, y) = y

-- Problema 3: data una coppia (x, y), restituirne il primo elemento
-- Funzione: first (x, y)
-- Esempio: first (2, 3) = 2

first (x, y) = x

-- Problema 2: data una lista di numeri, restituire una coppia (len, n) dove len è la lunghezza delle sottoliste crescenti di lunghezza massimale, e n è il loro numero
-- Funzione: infoincr l
-- Esempio: infoincr (1 : 2 : 3 : 2 : 4 : 0 : 1 : 2 : 0 : []) = (3, 2)

infoincr [] = (0, 1)
infoincr (h : t) =
  if (len (first_growing h t) > first (infoincr t))
    then (len (first_growing h t), 1)
    else
      if (len (first_growing h t) == first (infoincr t))
        then (first (infoincr t), second (infoincr t) + 1)
        else infoincr t

-- Problema 1: data una lista di numeri, restituire il numero di sottoliste crescenti di lunghezza massimale
-- Soluzione: numincr l
-- Esempio: numincr (1 : 2 : 3 : 2 : 4 : 0 : 1 : 2 : 0 : []) = 2

numincr l = second (infoincr l)

----------------------------------------------------

-- Problema 3

max_num x y = if (x > y) then x else y

-- Problema 2

sum_num_list n [] = n
sum_num_list n (hd : tl) = hd + (sum_num_list n tl)

-- Problema 1

f [] = 0
f (hd : tl) = max_num (sum_num_list hd tl) (f tl)