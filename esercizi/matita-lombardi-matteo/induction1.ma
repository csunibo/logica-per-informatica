(* Author: Matteo Lombardi *)

include "arithmetics/nat.ma".

(*
list ::= E | C n list
*)

inductive list : Type[0] ≝
    E : list
  | C : nat → list → list.
  
(*
concat E l2 = l2
concat (C hd tl) l2 = C hd (concat tl l2)
*)
  
let rec concat l1 l2 on l1 ≝
  match l1 with
  [ E ⇒ l2
  | C hd tl ⇒ C hd (concat tl l2)
  ].

(*
len E = 0
len (C hd tl) = 1 + len tl
*)

let rec len l on l ≝
  match l with
  [ E ⇒ 0
  | C hd tl ⇒ 1 + len tl
  ].
  
theorem len_concat:
  ∀ l1, l2. len (concat l1 l2) = len l1 + len l2.
assume l1 : list
we proceed by induction on l1 to prove
  (∀ l2. len (concat l1 l2) = len l1 + len l2).
case E
  we need to prove
    (∀ l2. len (concat E l2) = len E + len l2)
  that is equivalent to
    (∀ l2. len l2 = 0 + len l2)
  that is equivalent to
    (∀ l2. len l2 = len l2)
  done
  
case C (h : nat) (t : list)
  suppose
    (∀ l2. len (concat t l2) = len t + len l2) (II)
  we need to prove
    (∀ l2. len (concat (C h t) l2) = len (C h t) + len l2)
  that is equivalent to
    (∀ l2. 1 + len (concat t l2) = 1 + len t + len l2)
  assume l2 : list
  by II
done
qed.

(*
In n E ⇔ False
In n (C hd tl) ⇔ n = hd ∨ In n tl
*)

let rec In n l on l ≝
  match l with
  [ E ⇒ False
  | C hd tl ⇒ n = hd ∨ In n tl
  ].

theorem In1:
  ∀ l1, l2, n. In n l1 → In n (concat l1 l2).
assume l1: list
we proceed by induction on l1 to prove
  (∀ l2, n. In n l1 → In n (concat l1 l2))
case E
  we need to prove
    (∀ l2, n. In n E → In n (concat E l2))
  that is equivalent to
    (∀ l2, n. False → In n l2)
  assume l2: list
  assume n: nat
  suppose False (Abs)
  cases Abs (* questa riga dall'assurdo conclude qualsiasi cosa *)

case C (hd : nat) (tl : list)
  suppose
    (∀ l2, n. In n tl → In n (concat tl l2)) (II)
  we need to prove
    (∀ l2, n. In n (C hd tl) → In n (concat (C hd tl) l2))
  that is equivalent to
    (∀ l2, n. n = hd ∨ In n tl → In n (C hd (concat tl l2)))
  that is equivalent to
    (∀ l2, n. n = hd ∨ In n tl → n = hd ∨ In n (concat tl l2))
  assume l2: list
  assume n: nat
  suppose (n = hd ∨ In n tl) (H)
  we proceed by cases on H to prove
    (n = hd ∨ In n (concat tl l2))
  case or_introl
    suppose (n = hd) (EQ)
    by or_introl, EQ
  done
  case or_intror
    suppose (In n tl) (K)
    by or_intror, II, K
  done
qed.

theorem In2:
  ∀ l1, l2, n. In n l2 → In n (concat l1 l2).
assume l1: list
we proceed by induction on l1 to prove
  (∀ l2, n. In n l2 → In n (concat l1 l2))
case E
  we need to prove
    (∀ l2, n. In n l2 → In n (concat E l2))
  that is equivalent to
    (∀ l2, n. In n l2 → In n l2)
  done

case C (hd : nat) (tl : list)
  suppose
    (∀ l2, n. In n l2 → In n (concat tl l2)) (II)
  we need to prove
    (∀ l2, n. In n l2 → In n (concat (C hd tl) l2))
  that is equivalent to
    (∀ l2, n. In n l2 → In n (C hd (concat tl l2)))
  that is equivalent to
    (∀ l2, n. In n l2 → n = hd ∨ In n (concat tl l2))
  assume l2: list
  assume n: nat
  suppose (In n l2) (H)
  by or_intror, H, II
  done
qed.

theorem In12:
  ∀ l1, l2, n. In n (concat l1 l2) → In n l1 ∨ In n l2.
assume l1: list
we proceed by induction on l1 to prove
  (∀ l2, n. In n (concat l1 l2) → In n l1 ∨ In n l2)
case E
  we need to prove
    ((∀ l2, n. In n (concat E l2) → In n E ∨ In n l2))
  that is equivalent to
    ((∀ l2, n. In n l2 → False ∨ In n l2))
  by or_intror
  done
case C (hd: nat) (tl: list)
  suppose
    (∀ l2, n. In n (concat tl l2) → In n tl ∨ In n l2) (II)
  we need to prove
    (∀ l2, n. In n (concat (C hd tl) l2) → In n (C hd tl) ∨ In n l2)
  that is equivalent to
    (∀ l2, n. In n (C hd (concat tl l2)) → 
      (n = hd ∨ In n tl) ∨ In n l2)
  that is equivalent to
    (∀ l2, n. n = hd ∨ In n (concat tl l2) → 
      (n = hd ∨ In n tl) ∨ In n l2)
  assume l2: list
  assume n: nat
  suppose (n = hd ∨ In n (concat tl l2)) (OR)
  we proceed by cases on OR to prove
    ((n = hd ∨ In n tl) ∨ In n l2)
  case or_introl
    suppose (n = hd) (EQ)
    by or_introl, EQ
  done
  
  case or_intror
    suppose (In n (concat tl l2)) (K)
    by II, K we proved (In n tl ∨ In n l2) (OR2)
    we proceed by cases on OR2 to prove
      ((n = hd ∨ In n tl) ∨ In n l2)
    case or_introl
      suppose (In n tl) (InT)
      by or_introl, or_intror, InT
    done
    case or_intror
      suppose (In n l2) (Inl2)
      by or_intror, Inl2
    done
qed.