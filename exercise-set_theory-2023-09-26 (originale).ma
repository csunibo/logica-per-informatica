
(**************************************************************************)
(*       ___                                                              *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||         The HELM team.                                      *)
(*      ||A||         http://helm.cs.unibo.it                             *)
(*      \   /                                                             *)
(*       \ /        This file is distributed under the terms of the       *)
(*        v         GNU General Public License Version 2                  *)
(*                                                                        *)
(**************************************************************************)




(*

 Componenti del gruppo (completare):

 * Nome1: ...
 * Cognome1: ...
 * Numero di matricola1: ...

 * Nome2: ...
 * Cognome2: ...
 * Numero di matricola2: ...

*)

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

notation "'ABSURDUM' A" non associative with precedence 89 for @{'absurdum $A}.
interpretation "ex_false" 'absurdum A = (False_ind ? A).

(* Da qui in avanti riempite i puntini e fate validar quello che scrivete
   a Matita usando le icone con le frecce. *)

(* Exercise 1 *)
theorem reflexivity_inclusion: ∀A. A ⊆ A.
 assume A:set (* Ora dobbiamo dimostrare A ⊆ A, guarda il goal in alto a destra, è cambiato! *)
 we need to prove (∀Z. Z ∈ A → Z ∈ A) (ZA_to_ZA) (* da ora stiamo provando 'ZA_to_ZA' (guarda in alto a destra (Matita ha aggiunto un altra finestrella di dimostrazione), fino al relativo 'done' *)
  assume Z:…
  suppose (Z ∈ A) (ZA) 
  by ZA done
  (* fine della prova di 'ZA_to_ZA' (guarda in alto a destra, Matita ha chiuso la finestrella di dimostrazione che aveva aperto),
     ora l'abbiamo guadagnata tra le ipotesi (ora compare nella lista in alto a destra)!
   Continuiamo con la prova del nostro teorema *)
 by ax_inclusion2, … done (* Quale ipotesi devo combinare con l'assioma? *)
qed.


(* Exercize 2 *)
theorem empty_absurd: ∀X, A. X ∈ ∅ → X ∈ A.
 assume X:set
 assume …: set
 suppose … (X_in_empty)
 by ax_empty, … we proved False (contraddizione) (* Andate a guardare cosa dice l'assioma ax_empty *)
 using (ABSURDUM contraddizione) done
qed.

(* Exercise 3 *) 
theorem intersection_idempotent: ∀A. A ∩ A = A.
 assume A: … (* Da ora stiamo provando A ∩ A = A *)
 we need to prove (∀Z. Z ∈ A ∩ A ⇔ Z ∈ A) (main) (* da ora stiamo provando 'main' (Matita ha aperto una nuova finestrella di dimostrazione), fino al relativo 'done' *)
  assume …: set (* Ora dobbiamo dimostrare Z ∈ A ∩ A ⇔ Z ∈ A, guarda il goal in alto a destra *)
  (* Dimostriamo le due implicazioni:
     Da destra a sinistra: *)
  we need to prove (Z∈A→Z∈A∩A) (right_to_left) (* da ora stiamo provando 'right_to_left' (nuova finestrella), fino al relativo 'done' *)
    suppose …(ZA)
    by conj, … we proved (Z ∈ A ∧ Z ∈ A) (ZA_and_ZA)
    by ax_intersect2, … done (* Andate a guardare cosa dice l'assioma 'ax_intersect2' *)
  (* fine della prova di 'right_to_left' (Matita ha chiuso la finestrella di prima),
     ora l'abbiamo guadagnata tra le ipotesi (ora compare nella lista in alto a destra)!
   Continuiamo con la prova di 'main' *)
  (* Da sinistra a destra: *)
  we need to prove … (left_to_right) (* da ora stiamo provando 'left_to_right' (nuova finestrella), fino al relativo 'done' *)
   suppose … (Z_A_inters_A)
   by ax_intersect1, Z_A_inters_A we have (Z ∈ A) (ZA1) and (Z ∈ A) (ZA2)
   by … done
   (* fine della prova di 'left_to_right',
      ora l'abbiamo guadagnata tra le ipotesi!
   Continuiamo con la prova di 'main' *)
  by …, left_to_right, right_to_left done
  (* fine della prova di 'main',
      ora l'abbiamo guadagnata tra le ipotesi (guarda la lista)!
  Continuiamo con la prova del nostro teorema *)
 by …, main done
qed.

(* Exercise 4 *)
theorem intersect_empty: ∀A. A ∩ ∅ = ∅.
 assume …
 we need to prove (∀Z. Z∈A∩∅⇔Z∈∅) (II)
   assume …
   we need to prove (Z∈A∩∅ → Z ∈∅) (I1)
     suppose … (Ze)
     by Ze, … we have (Z ∈ A) (ZA) and (Z∈∅) (ZE)
     by ZE done
   we need to prove … (I2)
     suppose … (ZE)
     by ZE, ax_empty we proved … (contraddizione)
     using (ABSURDUM …) done
   by … done
 by II, …
done
qed. 

(* Exercise 5 *)
theorem transitivity_inclusion: ∀A,B,C. A ⊆ B → B ⊆ C → A ⊆ C.
 assume …
 … B:set
 …
 suppose (A ⊆ B) (AB)
 suppose … (BC)
 we need to prove (∀Z. Z ∈ A → Z ∈ C) (ZAtoZC)
  …
  suppose … (ZA)
  by AB, ax_inclusion1, ZA we proved … (ZB)
  by … done (* Cosa dovete dimostrare (guardate il goal)? Che ipotesi avete a disposizione? *) 
 by  ax_inclusion2, … done
qed.

(* Exercise 6 *)
theorem antisymmetry_inclusion: ∀A,B. A ⊆ B → B ⊆ A → A = B.
 …
 assume B: set
 suppose … (AB)
 suppose (B ⊆ A) (BA)
 we need to prove (∀Z. Z ∈ A ⇔ Z ∈ B) (P)
  …
  by AB, ax_inclusion1 we proved … (AB')
  by …  we proved (Z ∈ B → Z ∈ A) (BA')
  by … done
 by P, … done (* Quale assioma devo utilizzare? *) 
qed.

(* Exercise 7 *)
theorem intersect_commutative: ∀A,B. A ∩ B = B ∩ A.
 …
 …
 we need to prove (∀Z. Z ∈ A ∩ B ⇔ Z ∈ B ∩ A) (II)
   …
   (* Facciamo prima l'implicazione da sinistra a destra: *)
   we need to prove … (I1)
     suppose … (ZAB)
     we need to prove (Z ∈ B ∩ A)
      by ax_intersect1,ZAB we have (Z ∈ A) (ZA) and … (ZB)
      by …,ax_intersect2 done
      (* Ora che abbiamo finito l'implicazione =>, cosa manca da fare? Guarda il goal *)
   we need to prove … (I2)
     suppose … (ZBA)
     we need to prove …
     by … we have (Z ∈ B) (ZB) and (Z∈A) (ZA)
     by ZA, ZB, … done
   by …,I1,I2 done
 by … done
qed.
