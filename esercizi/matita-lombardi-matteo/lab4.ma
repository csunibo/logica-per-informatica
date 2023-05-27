(* Author: Matteo Lombardi *)

(* Esercizio 1
   ===========
   Dimostrare l'associatività della somma per induzione strutturale su x.
*)
theorem plus_assoc: ∀x,y,z. plus x (plus y z) = plus (plus x y) z.
 (* Possiamo iniziare fissando una volta per tutte le variabili x,y,z
    A lezione vedremo il perchè. *)
 assume x : nat
 assume y : nat
 assume z : nat
 we proceed by induction on x to prove (plus x (plus y z) = plus (plus x y) z)
 case O
  (* Scriviamo cosa deve essere dimostrato e a cosa si riduce eseguendo le
     definizioni. *)
  we need to prove (plus O (plus y z) = plus (plus O y) z)
  that is equivalent to (plus y z = plus y z)
  (* done significa ovvio *)
  done
 case S (w: nat)
  (* Chiamiamo l'ipotesi induttiva IH e scriviamo cosa afferma
     Ricordate: altro non è che la chiamata ricorsiva su w. *)
  by induction hypothesis we know (plus w (plus y z) = plus (plus w y) z) (IH)
  we need to prove (plus (S w) (plus y z) = plus (plus (S w) y) z)
  that is equivalent to (S (plus w (plus y z)) = plus (S (plus w y)) z)
  (* by IH done significa ovvio considerando l'ipotesi IH *)
  by IH done
qed.

(* Esercizio 2
   ===========

   Definire il linguaggio degli alberi binari (= dove ogni nodo che non è una
   foglia ha esattamente due figli) le cui foglie siano numeri naturali.

   tree_nat ::= "Leaf" nat | "Node" nat nat
*)

inductive tree_nat : Type[0] ≝
   Leaf : nat → tree_nat
 | Node : tree_nat → tree_nat → tree_nat.

(* Il seguente albero binario ha due foglie, entrambe contenenti uni. *)
definition one_one_tree : tree_nat ≝ Node (Leaf one) (Leaf one).

(* Definite l'albero       /\
                          0 /\
                           1  2  *)
definition zero_one_two_tree : tree_nat ≝
 Node (Leaf O) (Node (Leaf one) (Leaf two)).


(* Esercizio 3
   ===========

   Definire la funzione `rightmost` che, dato un `tree_nat`, restituisca il
   naturale contenuto nella foglia più a destra nell'albero. *)

let rec rightmost tree on tree ≝
  match tree with
  [ Leaf n ⇒ n
  | Node tree1 tree2 ⇒ rightmost tree2
  ].

theorem test_rightmost : rightmost zero_one_two_tree = two.
done. qed.


(* Esercizio 4
   ============

   Definire la funzione `visit` che, dato un `tree_nat`, calcoli la `list_nat`
   che contiene tutti i numeri presenti nelle foglie dell'albero in input,
   nell'ordine in cui compaiono nell'albero da sinistra a destra.

   Suggerimento: per definire tree_nat usare la funzione `append` già definita
   in precedenza.

   Esempio: `visit zero_one_two_tree = Cons O (Cons one (Cons two Nil))`.
*)

let rec visit T on T ≝
 match T with
 [ Leaf n ⇒ Cons n Nil
 | Node T1 T2 ⇒ append (visit T1) (visit T2)
 ].

theorem test_visit : visit zero_one_two_tree = Cons O (Cons one (Cons two Nil)).
done. qed.


(* Esercizio 5
   ===========

   La somma di tutti i numeri nella concatenazione di due liste è uguale
   alla somma delle somme di tutti i numeri nelle due liste. *)

theorem sum_append: ∀L1,L2. sum (append L1 L2) = plus (sum L1) (sum L2).
 assume L1 : list_nat
 assume L2 : list_nat
 we proceed by induction on L1 to prove (sum (append L1 L2) = plus (sum L1) (sum L2))
 case Nil
  we need to prove (sum (append Nil L2) = plus (sum Nil) (sum L2))
  that is equivalent to (sum L2 = plus O (sum L2))
  done
  case Cons (N: nat) (L: list_nat)
  by induction hypothesis we know (sum (append L L2) = plus (sum L) (sum L2)) (IH)
  we need to prove (sum (append (Cons N L) L2) = plus (sum (Cons N L)) (sum L2))
  that is equivalent to (sum (Cons N (append L L2)) = plus (plus N (sum L)) (sum L2))
  that is equivalent to (plus N (sum(append L L2)) = plus (plus N (sum L)) (sum L2))
  (* Per concludere servono sia l'ipotesi induttiva IH che il teorema plus_assoc
     dimostrato prima. Convincetevene

     Nota: se omettete IH, plus_assoc o entrambi Matita ci riesce lo stesso
     Rendere stupido un sistema intelligente è complicato... Tuttavia non
     abusatene: quando scrivete done cercate di avere chiaro perchè il teorema
     è ovvio e se non vi è chiaro, chiedete. *)
  by IH, plus_assoc done
qed.

(* La funzione `plusT` che, dato un `tree_nat`, ne restituisce la
   somma di tutte le foglie. *)
let rec plusT T on T ≝
 match T with
 [ Leaf n ⇒ n
 | Node t1 t2 ⇒ plus (plusT t1) (plusT t2)
 ].


(* Esercizio 6
   ===========

   Iniziare a fare l'esercizio 7, commentando quel poco che c'è dell'esercizio 6
   Nel caso base vi ritroverete, dopo la semplificazione, a dover dimostrare un
   lemma non ovvio. Tornate quindi all'esercizio 3 che consiste nell'enunciare e
   dimostrare il lemma. *)

lemma plus_O: ∀N. N = plus N O.
  assume N : nat
  we proceed by induction on N to prove (N = plus N O)
  case O
    we need to prove (O = plus O O)
    that is equivalent to (O=O)
    done
  case S (x : nat)
    by induction hypothesis we know (x = plus x O) (II)
    we need to prove (S x = plus (S x) O)
    that is equivalent to (S x = S (plus x O))
    by II
    done
qed.
(* Esercizio 7
   ===========

   Dimostriamo che la `plusT` è equivalente a calcolare la `sum` sul risultato
   di una `visit`. *)


theorem plusT_sum_visit: ∀T. plusT T = sum (visit T).
 assume T : tree_nat
 we proceed by induction on T to prove (plusT T = sum (visit T))
 case Leaf (N : nat)
  we need to prove (plusT (Leaf N) = sum (visit (Leaf N)))
  that is equivalent to (N = sum (Cons N Nil))
  that is equivalent to (N = plus N (sum Nil))
  that is equivalent to (N = plus N O)
  (* Ciò che dobbiamo dimostrare non è ovvio (perchè?). Per proseguire,
     completate l'esercizio 6 enunciando e dimostrando il lemma che vi serve
     Una volta risolto l'esercizio 6, questo ramo diventa ovvio usando il lemma.*)
  by plus_O done
 case Node (T1:tree_nat) (T2:tree_nat)
  by induction hypothesis we know (plusT T1 = sum (visit T1)) (IH1)
  by induction hypothesis we know (plusT T2 = sum (visit T2)) (IH2)
  we need to prove (plusT (Node T1 T2)=sum (visit (Node T1 T2)))
  that is equivalent to (plus (plusT T1) (plusT T2) = sum (append (visit T1) (visit T2)))
  (* Oltre alla due ipotesi induttive, di quale altro lemma dimostrato in
     precedenza abbiamo bisogno per concludere la prova?*)
  by IH1,IH2,sum_append done
qed.


(* Un altro modo di calcolare la somma di due numeri: per ricorsione strutturale
   sul secondo argomento.

   plus' m O = m
   plus' m (S x) = S (plus' m x)
*)
let rec plus' m n on n ≝
 match n with
 [ O ⇒ m
 | S x ⇒ S (plus' m x) ].


(* Esercizio 8
   ============

   Dimostriamo l'equivalenza dei due metodi di calcolo
   Vi servirà un lemma: capite quale e dimostratelo
*)

lemma plus_O': ∀y. y = plus' O y.
  assume y : nat
  we proceed by induction on y to prove (y = plus' O y)
  case O
    we need to prove (O = plus' O O)
    that is equivalent to (O = O)
    done
  case S (n : nat)
    by induction hypothesis we know (n = plus' O n) (II)
    we need to prove (S n = plus' O (S n))
    that is equivalent to (S n = S (plus' O n))
    by II
    done
qed.

lemma plus_S': ∀y,z. S (plus' z y) = plus' (S z) y.
  assume y : nat
  we proceed by induction on y to prove (∀z. S (plus' z y) = plus' (S z) y)
  case O
    we need to prove (∀z. S(plus' z O) = plus' (S z) O)
    that is equivalent to (∀z. S z = S z)
    done
  case S (g : nat)
    by induction hypothesis we know (∀z. S(plus' z g) = plus' (S z) g) (II)
    we need to prove (∀z. S (plus' z (S g)) = plus' (S z) (S g))
    that is equivalent to (∀z. S (S (plus' z g)) = S (plus' (S z) g))
    by II
    done
qed.


theorem plus_plus': ∀x,y. plus x y = plus' x y.
 (* Nota: la dimostrazione è più facile se andate per induzione su y perchè
    potrete riciclare un lemma già dimostrato.
    Se andate per induzione su x vi verrà lo stesso, ma in tal caso avrete
    bisogno di due lemmi, ognuno dei quali non ancora dimostrati. *)
 assume x: nat
 we proceed by induction on x to prove (∀y. plus x y = plus' x y)
 case O
  we need to prove (∀y. plus O y = plus' O y)
  that is equivalent to (∀y. y = plus' O y)
  by plus_O'
  done
 case S (z:nat)
  by induction hypothesis we know (∀y. plus z y = plus' z y) (II)
  we need to prove (∀y. plus (S z) y = plus' (S z) y)
  that is equivalent to (∀y. S (plus z y) = plus' (S z) y)
  by II, plus_S'
  done
qed.


(* Esercizio 9: se finite prima o volete esercitarvi a casa
   ========================================================

   Dimostriamo l'equivalenza dei due metodi di calcolo plus e plus',
   questa volta per induzione sul primo argomento x. Avrete bisogno di uno o
   più lemmi, da scoprire. Ovviamente, NON è consentito usare quanto dimostrato
   all'esercizio precedente

lemma …
qed.

theorem plus_plus_new: ∀x,y. plus x y = plus' x y.
…
(* Es*)ercizio 10,11,…
   =================

   Volete esercitarvi a casa su altre dimostrazioni facili come queste?
   Ecco due buoni spunti:

   1) definite la funzione che inserisce un numero in
      coda a una lista e usatela per definire la funzione rev che restituisce
      la lista ottenuta leggendo la lista in input dalla fine all'inizio
      Esempio:
       rev (Cons 1 (Cons 2 (Cons 3 Nil))) = (Cons 3 (Cons 2 (Cons 1 Nil)))
      Poi dimostrate che ∀L. sum (rev L) = sum L
      Per riuscirci vi serviranno una cascata di lemmi intermedi da enunciare
      e dimostrare
   2) definite una funzione leq_nat che dati due numeri naturali ritorni true
      sse il primo è minore o uguale al secondo; usatela per scrivere una funzione
      che aggiunga un elemento in una lista ordinata di numeri;
      poi usatela quest'ultima per definire una funzione "sort" che ordina una lista
      di numeri. Dimostrate che l'algoritmo è corretto procedendo
      come segue:
      a) definite, per ricorsione strutturale, il predicato ``X appartiene
         alla lista L''
      b) dimostrate che X appartiene all'inserimento di Y nella lista ordinata
         L sse X è uguale a Y oppure appartiene a L
      c) dimostrate che se X appartiene alla lista L allora appartiene alla
         lista sort L
      d) dimostrate anche il viceversa
      e) definite, per ricorsione strutturale, il predicato ``X è ordinata''
      f) dimostrate che se L è ordinata lo è anche la lista ottenuta inserendo
         X in L
      g) dimostrate che per ogni L, sort L è ordinata

      Nota: a)-e) sono esercizi semplici. Anche g) è semplice se asserite f)
      come assioma. La dimostrazione di f) invece è più difficile e
      potrebbe richiede altri lemmi ausiliari quali la transitività del
      predicato leq_nat
*)