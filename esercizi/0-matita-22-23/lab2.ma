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
  by BC, ax_inclusion1, ZB (* Osservate bene cosa deve essere dimostrato *)
 done
 by ZAtoZC, ax_inclusion2
done
qed.

(* Exercise 3 *)
theorem antisymmetry_inclusion: ∀A,B. A ⊆ B → B ⊆ A → A = B.
 assume A: set
 assume B: set
 suppose (A ⊆ B) (AB)
 suppose (B ⊆ A) (BA)
 we need to prove (∀Z. Z ∈ A ⇔ Z ∈ B) (P)
  assume Z: set
  by AB, ax_inclusion1 we proved (Z ∈ A → Z ∈ B) (AB')
  by BA, ax_inclusion1  we proved (Z ∈ B → Z ∈ A) (BA')
  by conj, AB', BA'
 done
 by ax_extensionality, P  (* Quale assioma devo utilizzare? *)
done
qed.

(* Exercise 4 *)
theorem intersection_idempotent_1: ∀A. A ⊆ A ∩ A.
 assume A: set
 we need to prove (∀Z. Z ∈ A → Z ∈ A ∩ A) (AinAA)
  assume Z: set
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
 assume A: set
 assume A': set
 assume B: set
 suppose (A ⊆ A') (H)
 we need to prove (∀Z. Z ∈ A ∩ B → Z ∈ A' ∩ B) (K)
  assume Z: set
  suppose (Z ∈ A ∩ B) (ZAB)
  by ax_intersect1, ZAB we proved (Z ∈ A ∧ Z ∈ B) (ZAZB)
  by ZAZB we have (Z ∈ A) (ZA) and (Z ∈ B) (ZB) (* Da un'ipotesi congiunzione si ricavano due ipotesi distinte *)
  by ax_inclusion1,ZA we proved (Z ∈ A') (ZA')
  by conj,ZA',ZB we proved (Z ∈ A' ∧ Z ∈ B) (ZAZB')
  by ax_intersect2,ZAZB' (* Cosa stiamo dimostrando? Che assioma serve? *)
 done
by ax_inclusion2,K
done
qed.

(* Exercise 6*)
theorem intersect_monotone_r: ∀A,B,B'. B ⊆ B' → A ∩ B ⊆ A ∩ B'.
 assume A: set
 assume B: set
 assume B': set
 suppose (B ⊆ B') (H)
 we need to prove (∀Z. Z ∈ A ∩ B → Z ∈ A ∩ B') (K)
  assume Z: set
  suppose (Z ∈ A ∩ B) (ZAB)
  by ax_intersect1, ZAB we proved (Z ∈ A ∧ Z ∈ B) (ZAZB)
  by ZAZB we have (Z ∈ A) (ZA) and (Z ∈ B) (ZB)
  by ax_inclusion1,ZB we proved (Z ∈ B') (ZB')
  by conj,ZA,ZB' we proved (Z ∈ A ∧ Z ∈ B') (ZAZB')
  by ax_intersect2,ZAZB'
 done
 by ax_inclusion2,K
done
qed.

(* Nuovi esercizi, secondo laboratorio *)

(* Exercise 7 *)
theorem union_inclusion: ∀A, B. A ⊆ A ∪ B.
  assume A: set
  assume B: set
  we need to prove (∀Z. Z ∈ A → Z ∈ A ∪ B) (I)
    assume Z: set
    suppose (Z∈A) (ZA)
    we need to prove (Z ∈ A ∨ Z ∈ B) (I1)
      by ZA,or_introl
    done
    by ax_union2, I1
  done
  by ax_inclusion2, I done
qed.

(* Exercise 8 *)
theorem union_idempotent: ∀A. A ∪ A = A.
 assume A: set
 we need to prove (∀Z. Z ∈ A ∪ A ⇔ Z ∈ A) (II)
 assume Z: set
  we need to prove (Z ∈ A ∪ A → Z ∈ A) (I1)
   suppose (Z ∈ A ∪ A)(Zu)
   by ax_union1, Zu we proved (Z ∈ A ∨ Z ∈ A) (Zor)
   we proceed by cases on Zor to prove (Z ∈ A)
    case or_introl
       suppose (Z∈A) (H)
       by H
    done
    case or_intror
       suppose (Z∈A) (H)
       by H
    done
  we need to prove (Z ∈ A → Z ∈ A ∪ A) (I2)
  suppose (Z∈A) (ZA)
   by ZA, or_introl we proved (Z ∈ A ∨ Z ∈ A) (Zor)
   by ax_union2, Zor
  done
  by conj, I1, I2
 done
 by II,ax_extensionality
done
qed.

(* Exercize 9 *)
theorem empty_absurd: ∀X, A. X ∈ ∅ → X ∈ A.
 assume X: set
 assume A: set
 suppose (X ∈ ∅) (XE)
 by ax_empty we proved False (bottom)
 using (ABSURDUM bottom)
done
qed.

(* Exercise 10 *)
theorem intersect_empty: ∀A. A ∩ ∅ = ∅.
 assume A: set
 we need to prove (∀Z. Z ∈ A ∩ ∅ ⇔ Z ∈ ∅) (II)
   assume Z: set
   we need to prove (Z ∈ A ∩ ∅ → Z ∈ ∅) (I1)
     suppose (Z ∈ A ∩ ∅) (Ze)
     we need to prove (Z ∈ ∅)
     by Ze, ax_intersect1 we have (Z ∈ A) (ZA) and (Z∈∅) (ZE)
     by ZE
   done
   we need to prove (Z ∈ ∅ → Z ∈ A ∩ ∅) (I2)
     suppose (Z ∈ ∅) (ZE)
     by ZE, ax_empty we proved False (bottom)
     using (ABSURDUM bottom)
   done
   by I1, I2, conj
 done
 by II, ax_extensionality
done
qed.

(* Exercise 11 *)
theorem union_empty: ∀A. A ∪ ∅ = A.
 assume A: set
 we need to prove (∀Z. Z ∈ A ∪ ∅ ⇔ Z ∈ A) (II)
   assume Z:set
   we need to prove (Z ∈ A → Z ∈ A ∪ ∅) (I1)
     suppose (Z ∈ A) (ZA)
     by or_introl, ZA we proved (Z ∈ A ∨ Z ∈ ∅) (Zor)
     by ax_union2,Zor
   done
   we need to prove (Z ∈ A ∪ ∅ → Z ∈ A) (I2)
     suppose (Z ∈ A ∪ ∅) (Zu)
     by ax_union1, Zu we proved (Z ∈ A ∨ Z ∈ ∅) (Zor)
     we proceed by cases on Zor to prove (Z ∈ A)
      case or_introl
        suppose (Z ∈ A) (H)
        by H done
      case or_intror
        suppose (Z ∈ ∅) (H)
         by ax_empty, H we proved False (bottom)
         using (ABSURDUM bottom)
      done
    by conj, I1, I2
  done
  by ax_extensionality, II
 done
qed.

(* Exercise 12 *)
theorem union_commutative: ∀A,B. A ∪ B = B ∪ A.
 assume A: set
 assume B: set
 we need to prove (∀Z. Z ∈ A ∪ B ⇔ Z ∈ B ∪ A) (II)
   assume Z: set
   we need to prove (Z ∈ A ∪ B → Z ∈ B ∪ A) (I1)
     suppose (Z ∈ A ∪ B) (ZAB)
     we need to prove (Z ∈ B ∪ A)
     we need to prove (Z ∈ B ∨ Z ∈ A) (I)
       by ZAB, ax_union1 we proved (Z∈A∨Z∈B) (Zor)
       we proceed by cases on Zor to prove (Z ∈ B ∨ Z ∈ A)
       case or_intror
         suppose (Z∈B) (H)
         by H,or_introl
       done
       case or_introl
         suppose (Z∈A) (H)
         by H, or_intror
       done  
   by I,ax_union2 done
   we need to prove (Z ∈ B ∪ A → Z ∈ A ∪ B) (I2)
     suppose (Z ∈ B ∪ A) (ZBA)
     we need to prove (Z ∈ A ∪ B)
     we need to prove (Z ∈ A ∨ Z ∈ B) (I)
       by ZBA, ax_union1 we proved (Z∈B∨Z∈A) (Zor)
       we proceed by cases on Zor to prove (Z ∈ A ∨ Z ∈ B)
       case or_intror
         suppose (Z∈A) (H)
         by H,or_introl
       done
       case or_introl
         suppose (Z∈B) (H)
         by H, or_intror
       done
   by I,ax_union2 done
  by I1,I2,conj
 done
 by ax_extensionality,II
done
qed.