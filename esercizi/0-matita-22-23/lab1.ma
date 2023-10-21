(* Author: Matteo Lombardi *)

(* Saltate le righe seguenti dove vengono dati gli assiomi e definite
   le notazioni e cercate Exercise 1. *)

include "basics/logic.ma".
include "basics/core_notation.ma".

notation "hvbox(A break ⇔ B)" left associative with precedence 30 for
@{'iff $A $B}.
interpretation "iff" 'iff A B = (iff A B).

(* set, ∈ *)
axiom set: Type[0].
axiom mem: set → set → Prop.
axiom incl: set → set → Prop.

notation "hvbox(a break ∈ U)" non associative with precedence 50 for
@{'mem $a $U}.
interpretation "mem" 'mem = mem.

notation "hvbox(a break ⊆ U)" non associative with precedence 50 for
@{'incl $a $U}.
interpretation "incl" 'incl = incl.

(* Extensionality *)
axiom ax_extensionality: ∀A, B. (∀Z. Z ∈ A ⇔ Z ∈ B) → A = B.

(* Inclusion *)
axiom ax_inclusion1: ∀A, B. A ⊆ B → (∀Z. Z ∈ A → Z ∈ B).
axiom ax_inclusion2: ∀A, B. (∀Z. Z ∈ A → Z ∈ B) → A ⊆ B.

(* Emptyset  ∅ *)
axiom emptyset: set.

notation "∅" non associative with precedence 90 for @{'emptyset}.
interpretation "emptyset" 'emptyset = emptyset.

axiom ax_empty: ∀X. (X ∈ ∅)→ False.

(* Intersection ∩ *)
axiom intersect: set → set → set.

notation "hvbox(A break ∩ B)" left associative with precedence 80 for
@{'intersect $A $B}.
interpretation "intersect" 'intersect = intersect.

axiom ax_intersect1: ∀A,B. ∀Z. (Z ∈ A ∩ B → Z ∈ A ∧ Z ∈ B).
axiom ax_intersect2: ∀A,B. ∀Z. (Z ∈ A ∧ Z ∈ B → Z ∈ A ∩ B).

(* Union ∪ *)
axiom union: set → set → set.

notation "hvbox(A break ∪ B)" left associative with precedence 70 for
@{'union $A $B}.
interpretation "union" 'union = union.

axiom ax_union1: ∀A,B. ∀Z. (Z ∈ A ∪ B → Z ∈ A ∨ Z ∈ B).
axiom ax_union2: ∀A,B. ∀Z. (Z ∈ A ∨ Z ∈ B → Z ∈ A ∪ B).

notation "'ABSURDUM' A" non associative with precedence 89 for @{'absurdum $A}.
interpretation "ex_false" 'absurdum A = (False_ind ? A).

(* Da qui in avanti riempite i puntini e fate validar quello che scrivete
   a Matita usando le icone con le frecce. *)

(* Exercise 1 *)
theorem reflexivity_inclusion: ∀A. A ⊆ A.
 assume A:set
 we need to prove (∀Z. Z ∈ A → Z ∈ A) (ZAtoZA)
  assume Z:set
  suppose (Z ∈ A) (ZA)
  by ZA (* Quale ipotesi serve? Osservate cosa bisogna dimostrare *)
 done
 by ax_inclusion2, ZAtoZA (* Quale ipotesi devo combinare con l'assioma? *)
done
qed.

(* Exercise 2 *)
theorem transitivity_inclusion: ∀A,B,C. A ⊆ B → B ⊆ C → A ⊆ C.
 assume A:set
 assume B:set
 assume C:set
 suppose (A ⊆ B) (AB)
 suppose (B ⊆ C) (BC)
 we need to prove (∀Z. Z ∈ A → Z ∈ C) (ZAtoZC)
  assume Z:set
  suppose (Z ∈ A) (ZA)
  by AB, ax_inclusion1, ZA we proved (Z ∈ B) (ZB)
  by BC, ax_inclusion1, ZB we proved (Z ∈ C) (ZC)(* Osservate bene cosa deve essere dimostrato *)
 done
 by ax_inclusion2, ZAtoZC
done
qed.

(* Exercise 3 *)
theorem antisymmetry_inclusion: ∀A,B. A ⊆ B → B ⊆ A → A = B.
 assume A:set
 assume B:set
 suppose (A ⊆ B) (AB)
 suppose (B ⊆ A) (BA)
 we need to prove (∀Z. Z ∈ A ⇔ Z ∈ B) (P)
  assume Z:set
  by AB, ax_inclusion1 we proved (Z ∈ A → Z ∈ B) (AB')
  by BA, ax_inclusion1 we proved (Z ∈ B → Z ∈ A) (BA')
  by conj, AB', BA'
 done
 by ax_extensionality, P  (* Quale assioma devo utilizzare? *)
done
qed.

(* Exercise 4 *)
theorem intersection_idempotent_1: ∀A. A ⊆ A ∩ A.
 assume A:set
 we need to prove (∀Z. Z ∈ A → Z ∈ (A ∩ A)) (AinAA)
  assume Z:set
  suppose (Z ∈ A) (ZA)
  we need to prove (Z ∈ A ∧ Z ∈ A) (ZAZA)
   by conj, ZA (* Il teorema conj serve per dimostrare una congiunzione (un "and" ∧) *)
  done
  by ax_intersect2, ZAZA (* Cosa stiamo dimostrando? Che assioma serve? *)
 done
 by ax_inclusion2, AinAA
done
qed.

(* Exercise 5*)
theorem intersect_monotone_l: ∀A,A',B. A ⊆ A' → A ∩ B ⊆ A' ∩ B.
 assume A:set
 assume A':set
 assume B:set
 suppose (A ⊆ A') (AA')
 we need to prove (∀Z. Z ∈ A ∩ B → Z ∈ A' ∩ B) (P)
  assume Z:set
  suppose (Z ∈ A ∩ B) (F)
  by ax_intersect1, F we proved (Z ∈ A ∧ Z ∈ B) (ZAZB)
  by ZAZB we have (Z ∈ A) (ZA) and (Z ∈ B) (ZB) (* Da un'ipotesi congiunzione si ricavano due ipotesi distinte *)
  by ax_inclusion1, AA' we proved (Z ∈ A') (ZA')
  by conj  we proved (Z ∈ A' ∧ Z ∈ B) (ZAZB')
  by ax_intersect2 (* Cosa stiamo dimostrando? Che assioma serve? *)
 done
by ax_inclusion2, P
done
qed.

(* Exercise 6*)
theorem intersect_monotone_r: ∀A,B,B'. B ⊆ B' → A ∩ B ⊆ A ∩ B'.
 assume A:set
 assume B:set
 assume B':set
 suppose (B ⊆ B') (BB')
 we need to prove (∀Z. Z ∈ A ∩ B → Z ∈ A ∩ B') (P)
  assume Z:set
  suppose (Z ∈ A ∩ B) (F)
  by ax_intersect1, F we proved (Z ∈ A ∧ Z ∈ B) (ZAZB)
  by ZAZB we have (Z ∈ A) (ZA) and (Z ∈ B) (ZB)
  by ax_inclusion1, BB' we proved (Z ∈ B') (ZB')
  by conj we proved (Z ∈ A ∧ Z ∈ B') (ZAZB')
  by ax_intersect2
 done
by ax_inclusion2, P
done
qed.