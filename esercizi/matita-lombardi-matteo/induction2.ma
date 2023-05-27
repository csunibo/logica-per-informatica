(* Author: Matteo Lombardi *)

include "arithmetics/nat.ma".

(* N ::= O | S N *)

inductive N : Type[0] ≝
    O: N
  | S: N → N.

(*
plus E m = m
plus (S n) m = S (plus n m)
*)

let rec plus n m on n ≝
  match n with
  [ O ⇒ m
  | S x ⇒ S (plus x m)
  ].
  
lemma plus_O:
  ∀ m. m = plus m O.
assume m: N
we proceed by induction on m to prove
  (m = plus m O)
case O
  we need to prove
    (O = plus O O)
  that is equivalent to
    (O = O)
  done
case S (x : N)
  suppose (x = plus x O) (II)
  we need to prove
    (S x = plus (S x) O)
  that is equivalent to
    (S x = S (plus x O))
  by II
done
qed.

lemma plus_s:
  ∀ m, x. S (plus m x) = plus m (S x).
assume m: N
we proceed by induction on m to prove
  (∀ x. S (plus m x) = plus m (S x))
case O
  we need to prove
    (∀ x. S (plus O x) = plus O (S x))
  that is equivalent to
    (∀ x. S x = S x)
done

case S (y : N)
  suppose (∀ x. S (plus y x) = plus y (S x)) (II)
  we need to prove
    (∀ x. S (plus (S y) x) = plus (S y) (S x))
  that is equivalent to
    (∀ x. S (S (plus y x)) = S (plus y (S x)))
  by II
done
qed.

theorem comm_plus:
  ∀ n, m. plus n m = plus m n.
assume n: N
we proceed by induction on n to prove
  (∀ m. plus n m = plus m n)
case O
  we need to prove
    (∀ m. plus O m = plus m O)
  that is equivalent to
    (∀ m. m = plus m O)
  by plus_O
done
case S (x : N)
  suppose (∀ m. plus x m = plus m x) (II)
  we need to prove (∀ m. plus (S x) m = plus m (S x))
  that is equivalent to
    (∀ m. S (plus x m) = plus m (S x))
  by plus_s, II
  done
qed.
    