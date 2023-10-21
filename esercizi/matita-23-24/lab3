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

 * Nome1: Orazio Andrea Capone
 * Cognome1:
 * Numero di matricola1:

 * Nome2: ...
 * Cognome2: ...
 * Numero di matricola2: ...

*)

(* Saltate le righe seguenti dove vengono dati gli assiomi e definite
   le notazioni e cercate Exercise 1. *)
   
notation > "hvbox(a break = b)" non associative with precedence 45 for
@{ eq set $a $b}.

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

(* Eliminazione dell'assurdo *)

notation "'ABSURDUM' A" non associative with precedence 89 for @{'absurdum $A}.
interpretation "ex_false" 'absurdum A = (False_ind ? A).

(* Unione *)

axiom union: set → set → set.

notation "hvbox(A break ∪ B)" left associative with precedence 70 for
@{'union $A $B}.
interpretation "union" 'union = union.

axiom ax_union1: ∀A,B. ∀Z. (Z ∈ A ∪ B → Z ∈ A ∨ Z ∈ B).
axiom ax_union2: ∀A,B. ∀Z. (Z ∈ A ∨ Z ∈ B → Z ∈ A ∪ B).

(* Insieme potenza *)

axiom powerset: set → set.

notation "hvbox(𝒫term 90 A)" non associative with precedence 70 for
@{'powerset $A}.
interpretation "powerset" 'powerset = powerset.

axiom pow1: ∀A,B. ( B ∈ powerset A → B ⊆ A ).
axiom pow2: ∀A,B. ( B ⊆ A → B ∈ powerset A ). 

(* Singoletto *)

axiom singleton: set → set.

notation "hvbox( { term 19 A} )" with precedence 90 for
@{'singleton $A}.
interpretation "singoletto" 'singleton = singleton.

axiom singleton1: ∀A,B. ( B ∈ {A} → B=A ).
axiom singleton2: ∀A,B. ( B=A → B ∈ {A} ).

(* Coppia non ordinata *)

notation "hvbox( ❴A,B❵ )" with precedence 70 for
@{'union ('singleton $A) ('singleton $B) }.


(* Da qui in avanti riempite i puntini e fate validar quello che scrivete
   a Matita usando le icone con le frecce. *)


(* Esercizio 1 *)

theorem unicita_del_vuoto: ∀V.( (∀Z. Z ∈ V → False) → V = ∅ ).
(* Perché questa formula esprime il fatto che l'insieme vuoto è unico ?? *)
  assume V:set
  suppose (∀Z:set.Z∈V→False) (V_no_elem)
  we need to prove (∀Z. (Z ∈ V → Z ∈ ∅)) (V_subset_empty)
    assume Z:set
    suppose (Z∈V) (Z_in_V)
    by Z_in_V, V_no_elem we proved False (contraddizione)
    using (ABSURDUM contraddizione) done
  we need to prove (∀Z. (Z ∈ ∅ → Z ∈ V)) (empty_subset_V)
    assume Z:set
    suppose (Z∈∅) (ZE)
    by ZE, ax_empty we proved False (F)
    using (ABSURDUM F) done
  by conj, V_subset_empty, empty_subset_V we proved (∀Z. (Z ∈ V ⇔ Z ∈ ∅)) (I)
  by I, ax_extensionality done
qed.
(* Hai notato qualcosa sulle dimostrazioni dei due 'we need to prove' precedenti ?
        Sono le stesse, basta giusto scambiare V e ∅ !!
        Perché ? Guarda l'assioma del vuoto e l'enunciato del teorema... *)

(* In maniera analoga si puo' dimostrare l'unicità degli altri insiemi che avete costruito (intersezione,
   insieme potenza, singoletto, coppia ordinata, prodotto cartediano, insieme delle funzioni, ecc).
   Per esempio, potete dimostrare la formula:
        ∀U,A,B.( (∀Z. Z ∈ U ⇔ (Z ∈ A ∨ Z ∈ B)) → U = A ∪ B ).
   che esprime (perché??) l'unicità dell'unione di insiemi fissati. *)



(* Nell'esercizio 2 e 3 avreste bisogno di usare i seguenti 4 lemmi *)

axiom Lemma1: ∀A. A⊆∅ → A=∅.
axiom Lemma2: ∀A. A=∅ → A⊆∅.
axiom Lemma3: ∀A. ∅⊆A.
axiom Lemma4: ∀A,B. A=B → A⊆B.


(* Esercizio 2 *)

(* Ricorda che `𝒫 ` si scrive con `\Pscr` *)

theorem pow_vuoto: 𝒫 (∅) = {∅} .
  we need to prove (∀Z. Z∈𝒫 (∅)→Z∈{∅})(left_to_right)
    assume Z:set
    suppose (Z∈𝒫 (∅))(PO)
    by pow1, PO we proved (Z⊆∅)(ZO)
    by Lemma1, ZO we proved (Z=∅) (I1)
    by I1, singleton2 done
  we need to prove (∀Z. Z∈{∅}→Z∈𝒫 (∅))(r_to_l)
    assume Z:set
    suppose (Z∈{∅}) (ZO)
    by ZO , singleton1 we proved (Z=∅)(ZE)
    by Lemma2, ZE we proved (Z⊆∅) (ZSE)
    by pow2, ZSE done
  by conj, left_to_right, r_to_l we proved (∀Z. Z∈𝒫 (∅)⇔Z∈{∅}) (I)
  by I, ax_extensionality done
qed.

(* Esercizio 3 *)

(* Ricorda che per l'insieme ❴∅,{X}❵ devi usare le parentesi graffe in grassetto,
   non quelle solite {∅,{X}}; fai copia ed incolla da sopra. *)

theorem power_singleton: ∀X. ❴∅,{X}❵ ⊆ 𝒫 {X} .
  assume X:set
  we need to prove (∀Z.  Z∈❴∅,{X}❵ → Z∈𝒫{X}) (I)
   assume Z:set
   suppose (Z∈❴∅,{X}❵) ( Z1 )
   (* Ricorda che {a,b} è zucchero sintattico per {a} ∪ {b} *)
   by ax_union1, Z1 we proved ( Z ∈ {∅} ∨ Z ∈ {{X}} ) (h_or)
   we need to prove ( Z ⊆ {X} ) (Z_sub_X)
    we proceed by cases on h_or to prove ( Z ⊆ {X} )
     case or_introl
       suppose (Z ∈ {∅}) (ZiO)
       by singleton1, ZiO we proved (Z=∅) (Zempty)
       by Lemma3 ,Zempty done (* Ricorda i lemmi di sopra *)
     case or_intror
       suppose (Z ∈ {{X}}) (ZiX)
       by singleton1, ZiX we proved (Z={X})(ZX)
       by Lemma4, ZX done
  by pow2, Z_sub_X done
  by I, ax_inclusion2 done
qed.


(* Esercizio 4 *)
theorem inclusion_intersect: ∀A,B,Z. Z ⊆ A ∧ Z ⊆ B ⇔ Z ⊆ A ∩ B.
  assume A:set
  assume B:set
  assume Z:set
  we need to prove (Z ⊆ A ∧ Z ⊆ B → Z ⊆ A ∩ B) (I1)
    suppose (Z ⊆ A ∧ Z ⊆ B)(ZAandZB)
    by (ZAandZB) we have (Z⊆A)(ZA) and (Z⊆B) (ZB)
    by ZA,ax_inclusion1 we proved (∀z. z∈Z→z∈A)(zA)
    by ZB,ax_inclusion1 we proved (∀z. z∈Z→z∈B)(zB)
    we need to prove (∀z. z∈Z→z∈A∩B)(I)
      assume z:set
      suppose (z∈Z)(zZ)
      by zA,z,zZ we proved (z ∈ A) (zA)
      by zB,z,zZ we proved (z ∈ B) (zB)
      by zA,zA,conj,ax_intersect2 done
    by I, ax_inclusion2 done
  we need to prove (Z ⊆ A ∩ B→Z ⊆ A ∧ Z ⊆ B ) (I2)
    suppose (Z ⊆ A ∩ B) (ZsubAB)
     by ZsubAB, ax_inclusion1 we proved (∀z. z∈Z→z∈A∩B) (ZiAB)
     we need to prove (∀z. z∈Z→z∈A) (ZA)
      assume z:set
      suppose (z∈Z) (zZ)
      by ZiAB, zZ we proved (z∈A∩B) (zAB)
      by zAB, ax_intersect1 we have (z∈A)(zA) and (z∈B)(zB)
      by zA done
     we need to prove (∀z. z∈Z→z∈B) (ZB)
      assume z:set
      suppose (z∈Z) (zZ)
      by ZiAB, zZ we proved (z∈A∩B) (zAB)
      by zAB, ax_intersect1 we have (z∈A)(zA) and (z∈B)(zB)
      by zB done
    by conj, ZA, ax_inclusion2 we proved (Z⊆A) (ZsA)
    by conj, ZB, ax_inclusion2 we proved (Z⊆B) (ZsB)
    by conj, ZsA, ZsB
    done
    by conj, I1, I2, ax_extensionality done
qed.




(* Exercise 5 *)

(* Nel corso della dimostrazione può essere utile utilizzare come Lemma l'esercizio 4 *)

theorem intersection_powerset: ∀A, B. (powerset A) ∩ (powerset B) = powerset (A ∩ B).
  assume A:set
  assume B:set
  we need to prove (∀Z. Z ∈ (powerset A) ∩ (powerset B) ⇔ Z ∈ powerset (A ∩ B)) (I)
    assume Z:set
    we need to prove (Z ∈ (powerset A) ∩ (powerset B) →  Z ∈ powerset (A ∩ B)) (I1)
      suppose (Z ∈ (powerset A) ∩ (powerset B)) (H1)
      by H1,ax_intersect1 we have (Z ∈ (powerset A)) (ZA) and (Z ∈ (powerset B)) (ZB)
      by ZA,pow1 we proved (Z ⊆ A) (ZsubA)
      by ZB,pow1 we proved (Z ⊆ B) (ZsubB)
      by conj, ZsubA, ZsubB we proved (Z⊆A∧Z⊆B) (zsAB)
      by inclusion_intersect,zsAB we proved (Z ⊆ A ∧ Z ⊆ B ⇔ Z ⊆ A ∩ B)(H2) 
      by H2 we have (Z ⊆ A ∧ Z ⊆ B → Z ⊆ A ∩ B) (H11) and (Z ⊆ A ∩ B → Z ⊆ A ∧ Z ⊆ B) (H12)
      by ZA,ZB,conj,H11 we proved (Z ⊆ A∩B) (ZAB)
      by ZAB,pow2 done
    we need to prove ( Z ∈ powerset (A ∩ B) → Z ∈ (powerset A) ∩ (powerset B)) (I2)
      suppose (Z ∈ powerset (A ∩ B)) (H1)
      by H1, pow1 we proved (Z⊆A∩B) (ZsubAB)
      by inclusion_intersect,ZsubAB we proved (Z ⊆ A ∧ Z ⊆ B ⇔ Z ⊆ A ∩ B)(H2) 
      by H2 we have (Z ⊆ A ∧ Z ⊆ B → Z ⊆ A ∩ B) (H11) and (Z ⊆ A ∩ B → Z ⊆ A ∧ Z ⊆ B) (H12)
      by H12, ZsubAB we proved (Z ⊆ A ∧ Z ⊆ B) (ZiAB)
      by ZiAB we have (Z ⊆ A) (ZA) and (Z ⊆ B) (ZB)
      by pow2, ZA we proved (Z∈powerset A)(PA)
      by pow2, ZB we proved (Z∈powerset B)(PB)
      by conj, ax_intersect2, PA, PB done
    by conj, I1, I2 done
  by I, ax_extensionality done
qed.
  
  
  





