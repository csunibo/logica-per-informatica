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

(* Union ∪ *)
axiom union: set → set → set.

notation "hvbox(A break ∪ B)" left associative with precedence 70 for
@{'union $A $B}.
interpretation "union" 'union = union.

axiom ax_union1: ∀A,B. ∀Z. (Z ∈ A ∪ B → Z ∈ A ∨ Z ∈ B).
axiom ax_union2: ∀A,B. ∀Z. (Z ∈ A ∨ Z ∈ B → Z ∈ A ∪ B).

(* Singoletto *)
axiom singleton: ∀A. ∃B. ∀Z. ((Z∈B → Z=A) ∧ (Z=A → Z∈B)).


(* Da qui in avanti riempite i puntini e fate validar quello che scrivete
   a Matita usando le icone con le frecce. *)

(* Exercise 1 *)
theorem union_inclusion: ∀A, B. A ⊆ A ∪ B.
  assume A: set
  assume B: …
  we need to prove (∀Z. Z ∈ A → Z ∈ A ∪ B) (I)
    assume …
    suppose (Z∈A) (ZA)
    we need to prove (Z ∈ A ∨ Z ∈ B) (I1)
    by ZA,or_introl
  done
  by … done
  by … done
qed.


(* Exercise 2 *)
theorem vuoto: ∀X. (∃Y.Y∈X) → (X=∅ → False).
  …
  suppose … (existsYinX)
  … (Xempty)
  by … let Y:set such that … (YinX)
  by ax_extensionality, (YinX) we proved … (YinEmpty)
  by …, (YinEmpty) we proved (False) (contraddizione)
  done
qed.

(*Excercise 3*)
theorem riscaldamento: ∃X. ∀Z. (Z∈X → False). (* Chi è questo X che dobbiamo costruire?? *)
  by … we proved (∀Z. Z∈… → False) (insieme_misterioso)
  by ex_intro, … done
qed.


(*Excercise 4*)

theorem in_to_subset: ∀A. (∃X. X ∈ A ) → ∃C. ( C ⊆ A ). (* tale C sarà il singoletto {X} *)
  …
  suppose …(existsXinA)
  by (existsXinA) let X:set such that …(XinA)
  by singleton we proved (∃singX. ∀Z. (…)) (exists_singleton_X)
  by … let SingX:set such that (∀Z. ((Z ∈ SingX → Z=X) ∧ (Z=X → Z ∈ SingX))) (singleton_X)
  we need to prove (SingX ⊆ A) (SingXinA)
    we need to prove (∀Z. Z ∈ SingX → Z ∈ A) (for_SingX_subset_A)
      …
      … (Z_in_SingX)
      by … we have (Z ∈ SingX → Z=X) (left_to_right) and (Z=X → Z ∈ SingX) (right_to_left)
      by …, Z_in_SingX we proved (Z = X) (ZeqX)
      by ZeqX, … done
    by …, for_SingX_subset_A done
  by … , … we proved (∃C:set.(C⊆A)) (eureka)
  …
qed. (* Osservate che avremmo potuto anche mettere 'done'
        direttamente al posto dell'ultimo 'we proved',
        invece che passare per 'eureka' *)
      

(* Exercise 5 *)
theorem union_empty: ∀A. A ∪ ∅ = A.
 …
 we need to prove … (II)
   …
   we need to prove … (I1)
     suppose … (ZA)
     by … we proved … (Zor)
     by ax_union2,Zor
   done
   we need to prove … (I2)
     suppose … (Zu)
     by … we proved (Z ∈ A ∨ Z ∈ ∅) (Zor)
     we proceed by cases on Zor to prove (Z ∈ A)
      case or_introl
        suppose … (H)
        by H done
      case or_intror
        suppose … (H)
         by … we proved False (bottom)
         …
      done
    by …
  done
  by …
 done
qed.


(* Exercise 6 *)
theorem distributivity1: ∀A,B,C. A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C).
 …
 we need to prove … (II)
  assume Z:set
  we need to prove … (I1)
   suppose (Z ∈(A ∪ B) ∩ (A ∪ C)) (Zint)
   by … we have … (Zu1) and … (Zu2)
   by … we proved (Z ∈ A ∨ Z ∈ B) (Zor1)
   by … we proved … (Zor2)
   we proceed by cases on Zor1 to prove …
   case or_introl
     suppose (Z∈A) (H)
     by or_introl,H,ax_union2 done
   case or_intror
    … (H)
    we proceed by cases on Zor2 to prove (Z∈A∪B∩C)
      case or_introl
        suppose (Z∈A) (H)
        by H,… done
      case or_intror
        suppose (Z∈C) (H1)
        by … we proved (Z∈B∩C) (K1)
        by K1,… we proved (Z∈A∨Z∈B∩C) (K2)
        by … done
  we need to prove … (I2)
   suppose (Z∈A∪B∩C) (Zu)
   by Zu,ax_union1 we proved … (Zor)
   we proceed by cases on Zor to prove …
   case or_introl
    …
    by …,ax_union2 we proved (Z∈ A ∪ B) (K1)
    by … we proved (Z∈ A ∪ C) (K2)
    by … done
   case or_intror
    suppose (Z∈B∩C)(H)
    by …  we have (Z ∈ B) (H1) and … (H2)
    by … we proved (Z∈ A∪B) (K1)
    by … we proved … (K2)
    by … done
  by … done
 by … done
qed.
