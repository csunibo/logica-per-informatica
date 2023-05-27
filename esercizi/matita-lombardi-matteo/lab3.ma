(* Author: Matteo Lombardi *)

(* ATTENZIONE
   ==========
   
   Non modificare la seguente riga che carica la definizione di uguaglianza.
*)
include "basics/logic.ma".


(* Esercizio 1
   ===========
   
   Definire il seguente linguaggio (o tipo) di espressioni riempiendo gli spazi.
   
   Expr :: "Zero" | "One" | "Minus" Expr | "Plus" Expr Expr | "Mult" Expr Expr
*)
inductive Expr : Type[0] ≝
| Zero: Expr
| One: Expr
| Minus: Expr → Expr
| Plus: Expr → Expr → Expr
| Mult: Expr → Expr → Expr
.

(* La prossima linea è un test per verificare se la definizione data sia
   probabilmente corretta. Essa definisce `test_Expr` come un'abbreviazione
   dell'espressione `Mult Zero (Plus (Minus One) Zero)`, verificando inoltre
   che l'espressione soddisfi i vincoli di tipo dichiarati sopra. Eseguitela. *)

definition test_Expr : Expr ≝ Mult Zero (Plus (Minus One) Zero).

(* Come esercizio, provate a definire espressioni che siano scorrette rispetto
   alla grammatica/sistema di tipi. Per esempio, scommentate la seguenti
   righe e osservate i messaggi di errore:
   
definition bad_Expr1 : Expr ≝ Mult Zero.
definition bad_Expr2 : Expr ≝ Mult Zero Zero Zero.
definition bad_Expr3 : Expr ≝ Mult Zero Plus.
*)

(* Esercizio 2
   ===========
   
   Definire il linguaggio (o tipo) dei numeri naturali.

   nat ::= "O" | "S" nat  
*)

inductive nat : Type[0] ≝
 O : nat
 | S : nat → nat
.

definition one : nat ≝ S O.
definition two : nat ≝ S (S O).
definition three : nat ≝ S (S (S O)).

(* Esercizio 3
   ===========
   
   Definire il linguaggio (o tipo) delle liste di numeri naturali.
   
   list_nat ::= "Nil" | "Cons" nat list_nat
   
   dove Nil sta per lista vuota e Cons aggiunge in testa un numero naturale a
   una lista di numeri naturali.
   
   Per esempio, `Cons O (Cons (S O) (Cons (S (S O)) Nil))` rappresenta la lista
   `[1,2,3]`.
*)

inductive list_nat : Type[0] ≝
 Nil : list_nat
 | Cons : nat → list_nat → list_nat
.

(* La seguente lista contiene 1,2,3 *)
definition one_two_three : list_nat ≝ Cons one (Cons two (Cons three Nil)).

(* Completate la seguente definizione di una lista contenente due uni. *)

definition one_one : list_nat ≝ Cons one (Cons one Nil).


(* Osservazione
   ===========
   
   Osservare come viene definita la somma di due numeri in Matita per
   ricorsione strutturale sul primo.
   
   plus O m = m
   plus (S x) m = S (plus x m) *)

let rec plus n m on n ≝
 match n with
 [ O ⇒ m
 | S x ⇒ S (plus x m) ].

(* Provate a introdurre degli errori nella ricorsione strutturale. Per esempio,
   omettete uno dei casi o fate chiamate ricorsive non strutturali e osservate
   i messaggi di errore di Matita. *)

(* Per testare la definizione, possiamo dimostrare alcuni semplici teoremi la
   cui prova consiste semplicemente nell'effettuare i calcoli. *)
theorem test_plus: plus one two = three.
done. qed.

(* Esercizio 4
   ===========

   Completare la seguente definizione, per ricorsione strutturale, della
   funzione `size_E` che calcola la dimensione di un'espressione in numero
   di simboli.
   
   size_E Zero = 1
   size_E One = 1
   size_E (Minus E) = 1 + size_E E
   ...
*)
let rec size_E E on E ≝
 match E with
  [    ⇒ one
  | One ⇒ one
  | Minus E ⇒ plus one (size_E E)
  | Plus E1 E2 ⇒ plus one (plus (size_E E1) (size_E E2))
  | Mult E1 E2 ⇒ plus one (plus (size_E E1) (size_E E2))
  ]
.

theorem test_size_E : size_E test_Expr = plus three three.
done. qed.

(* Esercizio 5
   ===========
   
   Definire in Matita la funzione `sum` che, data una `list_nat`, calcoli la
   somma di tutti i numeri contenuti nella lista. Per esempio,
   `sum one_two_three` deve calcolare sei.
*)

definition zero : nat ≝ O.

let rec sum L on L ≝
 match L with
 [ Nil ⇒ zero
 | Cons N TL ⇒ plus N (sum TL)]
.

theorem test_sum : sum one_two_three = plus three three.
done. qed.



(* Esercizio 6
   ===========
   
   Definire la funzione binaria `append` che, date due `list_nat` restituisca la
   `list_nat` ottenuta scrivendo in ordine prima i numeri della prima lista in
   input e poi quelli della seconda.
   
   Per esempio, `append (Cons one (Cons two Nil)) (Cons 0 Nil)` deve restituire
   `Cons one (Cons two (Cons 0 nil))`. *)
let rec append lista1 lista2 on lista1 ≝
 match lista1 with
 [ Nil ⇒ lista2
 | Cons N TL ⇒ append TL (Cons N lista2)]
.

theorem test_append : append (Cons one Nil) (Cons two (Cons three Nil)) = one_two_three.
done. qed.