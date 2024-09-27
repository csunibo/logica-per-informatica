/-

Riempire i seguenti dati con i membri del gruppo, formando gruppi da 2 (da 3 solo se autorizzati dal docente):
 
Matricola: __________________  Cognome: ____________________ Nome: _______________________  
Matricola: __________________  Cognome: ____________________ Nome: _______________________  
Matricola: __________________  Cognome: ____________________ Nome: _______________________  

Ricordatevi di salvare spesso, scaricando su disco il file modificato.
Nel caso il sistema smetta di funzionare, per farlo ripartire ricaricare la pagina premendo invio sulla URL della pagina.
Alla fine dell'esercitazione o del tempo consegnate il file seguendo i seguenti passi (1 e 3 dati da una shell):
 1.     rm ~/Downloads/Lean4WebDownload.lean
 2.     scaricate nuovamente il file
 3.     ~sacerdot/logica2223/ConsegnaLogica ~/Downloads/Lean4WebDownload.lean

Scendete alle linea 148 per iniziare l'esercitazione

-/

import Lean
open Lean
open Lean.Elab.Tactic

namespace matita

syntax "_last_hypothesis_" : term

elab_rules : term
 |`(term| _last_hypothesis_) => do ((← Lean.getLCtx).lastDecl.map (fun x ↦ x.toExpr)).getM -- bug here exclude recursive call to theorem

declare_syntax_cat matitaEquivalent

syntax "that " "is " "equivalent " "to " term : matitaEquivalent

syntax "assume " ident " : " term (matitaEquivalent)? : tactic

macro_rules
  | `(tactic| assume $ident : $type) => `(tactic| intro $ident:ident <;> guard_hyp _last_hypothesis_ :ₛ $type)
  | `(tactic| assume $ident : $type that is equivalent to $type₂) =>
    `(tactic| assume $ident : $type <;> change $type₂ at _last_hypothesis_)


syntax "suppose " term (matitaEquivalent)? (" as " ident)? : tactic

macro_rules
  | `(tactic| suppose $term as $ident) => `(tactic| intro $ident:ident <;> guard_hyp _last_hypothesis_ :ₛ $term)
  | `(tactic| suppose $term) => `(tactic| intro <;> guard_hyp _last_hypothesis_ :ₛ $term)
  | `(tactic| suppose $term that is equivalent to $type $[as $ident]? ) =>
    `(tactic| suppose $term $[as $ident]? <;> change $type at _last_hypothesis_)


theorem iff_e: ∀A B: Prop, (A ↔ B) → (A → B) ∧ (B → A) := by
 intros A B U ; cases U ; constructor <;> solve_by_elim

declare_syntax_cat matitaJust

syntax "thus "? ("by " ident,+)? : matitaJust

def matitaJust_to_solveByElimArg : TSyntax `matitaJust -> MacroM (TSyntax ``Lean.Parser.Tactic.SolveByElim.args)
  | `(matitaJust | thus by $[$terms],* ) => do
    let args ← terms.mapM fun x => `(Lean.Parser.Tactic.SolveByElim.arg| $x:ident)
    `(Lean.Parser.Tactic.SolveByElim.args| [$(args.push (← `(Lean.Parser.Tactic.SolveByElim.arg| _last_hypothesis_))),*, Or.inr, Or.inl, matita.iff_e, And.left, And.right])
  | `(matitaJust | by $[$terms],* ) =>
    `(Lean.Parser.Tactic.SolveByElim.args| [$[$terms:ident],*, Or.inr, Or.inl, matita.iff_e, And.left, And.right])
  | `(matitaJust | thus ) =>
    `(Lean.Parser.Tactic.SolveByElim.args| [_last_hypothesis_, Or.inr, Or.inl, matita.iff_e, And.left, And.right])
  | _ => -- panic! "xxx" -- thereis  the right throwXXX
    `(Lean.Parser.Tactic.SolveByElim.args| [Or.inr, Or.inl, matita.iff_e, And.left, And.right])

syntax matitaJust " done" : tactic

macro_rules
  | `(tactic | $mj:matitaJust done) => do
    `(tactic | solve_by_elim only $(← matitaJust_to_solveByElimArg mj))
  | `(tactic | done) => do
    `(tactic | solve_by_elim only [Or.inr, Or.inl, matita.iff_e, And.left, And.right])

syntax (matitaJust)? "we " " proved " term ("as " ident)? : tactic
syntax (matitaJust)? "we " " proved " term "as " ident "and " term "as " ident : tactic
syntax (matitaJust)? "let " ident ": " term "such " "that " term "as " ident : tactic

macro_rules
  | `(tactic | $mj:matitaJust we proved $term as $ident) => do
    let x ← matitaJust_to_solveByElimArg mj
    `(tactic | have $ident : $term := by solve_by_elim only $x)
  | `(tactic | $mj:matitaJust we proved $term) => do
    let x ← matitaJust_to_solveByElimArg mj
    `(tactic | have _ : $term := by solve_by_elim only $x)
  | `(tactic | we proved $term as $ident) =>
    `(tactic | have $ident : $term := by solve_by_elim only [Or.inr, Or.inl, matita.iff_e, And.left, And.right])
  | `(tactic | we proved $term) =>
    `(tactic | have _ : $term := by solve_by_elim only [Or.inr, Or.inl, matita.iff_e, And.left, And.right])
  | `(tactic | $mj:matitaJust we proved $term₁ as $ident₁ and $term₂ as $ident₂) =>
    `(tactic | $mj:matitaJust we proved $term₁ ∧ $term₂ <;> cases _last_hypothesis_ <;> case' _ $ident₁:ident $ident₂:ident => skip)
  | `(tactic | we proved $term₁ as $ident₁ and $term₂ as $ident₂) =>
    `(tactic | we proved $term₁ ∧ $term₂ <;> cases _last_hypothesis_ <;> case' _ $ident₁:ident $ident₂:ident => skip)
  | `(tactic | $mj:matitaJust let $ident₁ : $term₁ such that $term₂ as $ident₂) =>
    `(tactic | $mj:matitaJust we proved ∃$ident₁:ident : $term₁, $term₂ <;> cases _last_hypothesis_ <;> case' _ $ident₁:ident $ident₂:ident => skip)
  | `(tactic | let $ident₁ : $term₁ such that $term₂ as $ident₂) =>
    `(tactic | we proved ∃$ident₁:ident : $term₁, $term₂ <;> cases _last_hypothesis_ <;> case' _ $ident₁:ident $ident₂:ident => skip)

syntax "we " "need " "to " "prove " term (matitaEquivalent)? : tactic

macro_rules
 | `(tactic | we need to prove $term) =>
  `(tactic | guard_target =ₛ $term)
 | `(tactic | we need to prove $exp that is equivalent to $inf) =>
  `(tactic | we need to prove $exp <;> change $inf)

macro "we " "split " "the " "proof " : tactic => `(tactic| first | apply And.intro | apply Iff.intro)

macro "we " "claim " stmt:term "as " name:ident "by" colGt prf:tacticSeq : tactic => `(tactic|have $name : $stmt := by $prf)
macro "we " "claim " stmt:term                  "by" colGt prf:tacticSeq : tactic => `(tactic|have _ : $stmt := by $prf)

syntax "by " term "it " "suffices " "to " "prove " term : tactic

macro_rules
 | `(tactic| by $term:term it suffices to prove $arg) => `(tactic| apply $term:term <;> we need to prove $arg:term)

syntax "we " "choose " term "and " "prove " term (matitaEquivalent)? : tactic

macro_rules
 | `(tactic| we choose $term₁ and prove $term₂) => `(tactic| exists $term₁ <;> we need to prove $term₂)
 | `(tactic| we choose $term₁ and prove $term₂ that is equivalent to $term₃) =>
   `(tactic| we choose $term₁ and prove $term₂ <;> change $term₃)

macro "we " "proceed " "by " "cases " "on " name:ident "to " "prove " stmt:term : tactic => `(tactic|guard_target =ₛ $stmt <;> cases $name:term)

macro "we " "proceed " "by " "induction " "on " name:ident ": " type:term "to " "prove " stmt:term : tactic => `(tactic|guard_target =ₛ ∀$name : $type, $stmt <;> intro $name:ident <;> induction $name:term)

syntax "guard_hyps" "[" ("( " ident ": " term ") ")* "]" : tactic

macro_rules
 | `(tactic| guard_hyps []) => `(tactic| skip)
 | `(tactic| guard_hyps [($id : $term) $[($ids : $terms)]*]) => `(tactic| guard_hyp $id :ₛ $term <;> guard_hyps [$[($ids : $terms)]*])

syntax "case " ident
       ("( " ident ": " term ") ")*
       ("by " "induction " "hypothesis " "we " "know " term "as " ident)* : tactic

macro_rules
 | `(tactic| case $name:ident $[( $arg:ident : $type:term )]*
      $[by induction hypothesis we know $iitype:term as $ii:ident]*) =>
   `(tactic| case' $name:ident $[$arg:ident]* $[$ii:ident]* => guard_hyps [$[($arg : $type)]* $[($ii : $iitype)]*])

end matita

/-

Tutta la parte del file che precede questa linea implementa l'emulazione del software Matita in Lean. Ignoratela e non modificatela.

In Lean i commenti iniziano con -- e proseguono fino alla fine della riga, oppure come questo sono aperti da / seguito da - e chiusi da - seguito da /. In tal caso possono comprendere diverse linee.

Per digitare un simbolo matematico in Lean si digita \ seguito dal nome del simbolo. In particolare oggi avrete bisogno dei seguenti simboli:
  ∈   \mem
  ⊆   \subseteq
  ∀   \forall
  →   \to
  ↔   \iff
  ₁   \1
  ₂   \2
 ...  ...

Le prossime linee introducono gli assiomi della teoria degli insiemi, assieme alla notazione usata a lezione per le operazioni insiemistiche ∈ e ⊆. Leggetele senza modificarle, facendo caso ai commenti.

-/
namespace set_theory

-- Le prossime due righe, che non dovete capire, dicono che la nozione di set e il predicato di appartenenza mem (che indicheremo poi con ∈) sono enti primitivi. L'uguaglianza è già un simbolo primitivo noto a Lean e pertanto non viene dichiarato.
axiom set: Type
axiom mem: set → set → Prop

-- La prossima riga permette di scrivere l'appartenenza con il simbolo infisso ∈
infix:50 (priority := high) " ∈ " => mem

-- Assioma di estensionalità: se due insiemi hanno gli stessi elementi, allora sono uguali e viceversa. Invece di usare il se e solamente se formuliamo due assiomi, uno per direzione, per semplificarne l'uso nel tool.
axiom ax_extensionality1: ∀A B, (∀Z, Z ∈ A ↔ Z ∈ B) → A = B
axiom ax_extensionality2: ∀A B, A = B → (∀Z, Z ∈ A ↔ Z ∈ B)

-- Definizione di inclusione, che poi indicheremo con il simbolo infisso ⊆
def incl (A:set) (B:set) : Prop :=
 ∀Z, Z ∈ A → Z ∈ B

-- La prossima riga permette di scrivere l'inclusione con il simbolo infisso ⊆
infix:50 (priority := high) " ⊆ " => incl

/-

Da questo momento in avanti iniziano gli esercizi, che consistono nel completare alcune dimostrazioni.

Segue la sintassi dei comandi che avete a disposizione in Lean/Matita. Nella spiegazione P, Q, R indicano formule qualsiasi mentre i nomi delle ipotesi sono indicati con H, H1, ..., Hn.

Gli esercizi iniziano dopo la spiegazione della sintassi.

. assume A: set

  ∀-introduzione
  usato per dimostrare ∀A, P
  la conclusione diventa P

. suppose P as H

  →-introduzione
  usato per dimostrare P → Q
  la conclusione diventa Q
  si ha una nuova ipotesi P di nome H 
  dopo P è possibile specificare "that is equivalent to R" per espandere le definizioni contenute in P
  in tal caso la nuova ipotesi ha la forma R e non più P
  "as H" può essere omesso; in tal caso si può usare l'ipotesi solo al passo successivo con thus

. we split the proof

  ↔-introduzione
  usato per dimostare P ↔ Q
  bisogna aprire due sottoprove, la prima di P → Q e la seconda di Q → P
  le due sottoprove iniziano con . e sono indentate

. we need to prove P

  esplicita cosa si sta dimostrando
  non corrisponde a un passo logico
  può essere seguito da "that is equivalent to Q" per espandere le definizioni contenute in P

. by H1, ..., Hn done

  ∀-eliminazione + →-eliminazione + ↔-eliminazione
  si dimostra la conclusione del teorema combinando assieme le n ipotesi tramite un numero arbitrario di applicazione delle regole di eliminazione elencate subito sopra e ri-spiegate qua sotto
  si può usare "thus" prima di "by" per aggiugere l'ultima ipotesi introdotta, anonima o meno
  la dimostrazione (o la sotto-dimostrazione) è conclusa

  ∀-eliminazione: da un'ipotesi ∀x, P si ottiene P in un caso specifico, ottenuto sostituendo a x qualcosa
    Esempio: da ∀A, ∅ ⊆ A si può ricavare ∅ ⊆ ∅ sostituendo ad A l'insieme vuoto ∅
  →-eliminazione: da un'ipotesi P → Q e da un'ipotesi P si ricava Q
  ↔-eliminazione: da un'ipotesi P ↔ Q si ricava sia P → Q che Q → P

. by H1, ..., Hn we proved P as H

  come il caso precedente, ma invece di dimostrare la conclusione si ricava una nuova ipotesi P alla quale viene data il nome H
  dopo P è possibile specificare "that is equivalent to R" per espandere le definizioni contenute in P
  in tal caso la nuova ipotesi ha la forma R e non più P
  "as H" può essere omesso; in tal caso si può usare l'ipotesi solo al passo successivo con thus
  la conclusione da dimostrare non cambia

. by H it suffices to prove P

  ∀-eliminazione + →-eliminazione
  forma alternativa di ∀-eliminazione + →-eliminazione
  si use quando la conclusione corrente è Q e quando H, dopo l'applicazione di zero o più ∀-eliminazioni, ha la forma P → Q
  la nuova conclusione da dimostrare diventa P

-/

/-

Gli esercizi consistono nel sostituire ai puntini … le parti delle dimostrazioni omesse.
Al posto dei puntini potete dover inserire formule, nomi di ipotesi, comandi o sequenze di comandi.

-/

-- Esercizio 1: riflessività dell'inclusione
theorem reflexivity_inclusion: ∀A, A ⊆ A := by
 assume A: set
 we need to prove … that is equivalent to ∀Z, Z ∈ A → …
 assume Z: …
 suppose Z ∈ A
 thus done

-- non cancellare la seguente riga, utile per la correzione automatica
#check reflexivity_inclusion

-- Esercizio 2: transitività dell'inclusione
theorem transitivity_inclusion: ∀A B C, A ⊆ B → B ⊆ C → A ⊆ C := by
 assume A: set
 assume B: …
 assume …
 suppose A ⊆ B that is equivalent to ∀Z, Z ∈ A → Z ∈ B as H₁
 suppose … that is equivalent to … as H₂
 we need to prove A ⊆ C that is equivalent to …
 assume Z: set
 suppose …
 thus by H₁ we proved Z ∈ B        -- perchè? cosa afferma H₁ e l'ultima ipotesi anonima? fermati e rifletti
 thus by … done   -- perchè? fermati e rifletti

-- non cancellare la seguente riga, utile per la correzione automatica
#check transitivity_inclusion

-- Esercizio 3: due insiemi ognuno sottoinsieme dell'altro sono uguali
theorem subset_to_eq: ∀A B, A ⊆ B → B ⊆ A → A = B := by
 assume …
 …
 suppose A ⊆ B that is equivalent to ∀Z, … → Z ∈ B as H₁
 suppose … that is equivalent to … as H₂
 we need to prove A = B
 by ax_extensionality1 it suffices to prove ∀Z, Z ∈ A ↔ Z ∈ B  -- perchè? cosa afferma l'assioma di estensionalità? fermati e rifletti
 assume Z: set
 we split the proof
 . we need to prove Z ∈ A → Z ∈ B
   suppose …
   thus by H₁ done
 . we need to prove …
   suppose …
   thus by … done

-- non cancellare la seguente riga, utile per la correzione automatica
#check subset_to_eq

-- Esercizio 4: insiemi uguali sono sottoinsiemi uno dell'altro
theorem eq_to_subset1: ∀A B, A = B → A ⊆ B := by
 assume A: set
 …
 suppose …
 thus by ax_extensionality2 we proved ∀Z, Z ∈ A ↔ … as H
 we need to prove … that is equivalent to ∀X, X ∈ A → X ∈ B
 assume X: set
 suppose … as K
 thus by H we proved X ∈ A → X ∈ B
 thus by … done

#check eq_to_subset1

-- Esercizio 5: insiemi uguali sono sottoinsiemi uno dell'altro
-- Notate la stretta similitudine dell'enunciato con quello della prova precedente: anche le due dimostrazioni si assomiglieranno...
theorem eq_to_subset2: ∀A B, A = B → B ⊆ A := by
 …

#check eq_to_subset2

-- Esercizio 6: transitività dell'uguaglianza
-- La dimostrazione viene molto abbreviata se utilizziamo come lemmi tutti i teoremi dimostrati in precedenza
theorem transitivity_equality: ∀(A : set) B C, A = B → B = C → A = C := by
 assume A: set
 assume B: set
 assume C: set
 suppose A = B as H₁
 suppose B = C as H₂
 by eq_to_subset1, H₁ we proved A ⊆ B as H₁₁
 by … we proved B ⊆ A as H₁₂
 by eq_to_subset1, H₂ we proved … as H₂₁
 by … we proved C ⊆ B as H₂₂
 by H₁₁, H₂₁, transitivity_inclusion we proved A ⊆ C as K₁
 by … we proved C ⊆ A as K₂
 by subset_to_eq, K₁, K₂ done

#check transitivity_equality

end set_theory
