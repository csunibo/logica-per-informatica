(* Author: Matteo Lombardi *)

include "arithmetics/nat.ma".
include "basics/lists/list.ma".

(* Linea da ignorare *)
axiom daemon : False.

lemma true_or_false: ∀ b: bool. b = true ∨ b = false.
 //
qed.

(* Esercizio 7 *)

let rec isHead x l on l ≝
  match l with
  [ nil ⇒ false
  | cons y l' ⇒ eqb x y
  ].
  
let rec uniq l on l ≝
  match l with
  [ nil ⇒ nil ?
  | cons x l' ⇒
      if (isHead x (uniq l'))
      then (uniq l')
      else (cons ? x (uniq l'))
  ].
  
theorem isHead_uniql:
  ∀ x, y, l. isHead x l = true → isHead y l = true → x = y.
we need to prove (∀ x, y, l. isHead x l = true → isHead y l = true → x = y)
cases daemon
qed.

(* Dimostrazione, non funziona perchè il tipo ℕ non viene preso da matita
assume l : (list ℕ)
we proceed by induction on l to prove
  (∀ x, y. isHead x l = true → isHead y l = true → x = y)
case nil
  we need to prove
    (∀ x, y. isHead x nil = true → isHead y nil = true → x = y)
  that is equivalent to
    (∀ x, y. false = true → false = true → x = y)
  assume x : ℕ
  assume y : ℕ
  suppose (false = true) (abs) (* ipotesi assurda *)
  case daemon (* INTERROMPO LA PROVA IN QUANTO OVVIA,
                 DAL FALSO DIMOSTRO QUALUNQUE COSA*)

case cons (h : ℕ) (tl: (list ℕ))
  suppose (∀ x, y. isHead x tl = true → isHead y tl = true → x = y) (II)
  we need to prove
    (∀ x, y. isHead x (cons h tl) = true → isHead y (cons h tl) = true → x = y)
  that is equivalent to
    (∀ x, y. eqb x h = true → eqb y h = true → x = y)
  assume x: ℕ
  assume y: ℕ
  suppose (eqb x h = true) (H1)
  suppose (eqb y h = true) (H2)
  by eqb_true_to_eq, H1 we proved (x = h) (EQ1)
  by eqb_true_to_eq, H2 we proved (y = h) (EQ2)
  by EQ1, EQ2
done
qeb. *)

theorem isHead_uniq:
  ∀ l, x. isHead x l = isHead x (uniq l).
assume l : (list ℕ)
we proceed by induction on l to prove
  (∀ x. isHead x l = isHead x (uniq l))
case nil
  we need to prove
    (∀ x. isHead x (nil ?) = isHead x (uniq (nil ?)))
  that is equivalent to
    (∀ x. false = isHead x (nil ?))
  that is equivalent to
    (∀ x. false = false)
done

case cons (h : ℕ) (tl : (list ℕ))
  suppose (∀ x. isHead x tl = isHead x (uniq tl)) (II)
  we need to prove
    (∀ x. isHead x (cons ? h tl) = isHead x (uniq (cons ? h tl)))
  that is equivalent to
    (∀ x. eqb x h = isHead x
    (if (isHead h (uniq tl))
     then (uniq tl)
     else (cons ? h (uniq tl))))
  assume x : ℕ
  by true_or_false we proved
    (isHead h (uniq tl) = true ∨
     isHead h (uniq tl) = false) (TF)
  we proceed by cases on TF to prove
    (eqb x h = isHead x
    (if (isHead h (uniq tl))
     then (uniq tl)
     else (cons ? h (uniq tl))))
  case or_introl
    suppose (isHead h (uniq tl) = true) (IHT)
    we need to prove
      (eqb x h = isHead x (uniq tl)) (L)
    cases daemon (* INTERROMPO LA DIMOSTRAZIONE:
                    ovvio per IHT e isHead_uniq1 *)
    ]cases daemon
  case or_intror
    suppose (isHead h (uniq tl) = false) (IHF)
    we need to prove
      (eqb x h = isHead x (cons ? h (uniq tl))) (L)
    that is equivalent to (eqb x h = eqb x h)
    done
  done
qed.