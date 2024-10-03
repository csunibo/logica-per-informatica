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

Per prima cosa guardate come scrivere i nuovi simboli (riga 159 circa) e
quali nuovi assiomi avete a disposizioni (riga 190 circa). Poi riguardate
la spiegazione dei comandi "we split the proof" e "by", che ora gestiscono
anche il falso e la congiunzione (da riga 230 circa).
Infine dalla linea 472 circa trovate gli esercizi di oggi

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
  ∅   \emptyset
  ∩   \cap
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

-- Introduzione del simbolo ∅ per l'insieme vuoto
-- e corrispondente assioma nella versione che usa
-- il simbolo
axiom emptyset: set
notation:max "∅" => emptyset
axiom ax_empty: ∀X, (X ∈ ∅)→ False

-- Introduzione del simbolo ∩ per l'intersezione
-- e corrispondenti assiomi nella versione che usano
-- il simbolo
axiom intersect: set → set → set
infix:80 (priority := high) " ∩ " => intersect
axiom ax_intersect1: ∀A B, ∀Z, (Z ∈ A ∩ B → Z ∈ A ∧ Z ∈ B)
axiom ax_intersect2: ∀A B, ∀Z, (Z ∈ A ∧ Z ∈ B → Z ∈ A ∩ B)

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

  ∧-introduzione
  usato per dimostrare P ∧ Q
  bisogna aprire due sottoprove, la prima di P e la seconda di Q
  le due sottoprove iniziano con . e sono indentate

. we need to prove P

  esplicita cosa si sta dimostrando
  non corrisponde a un passo logico
  può essere seguito da "that is equivalent to Q" per espandere le definizioni contenute in P

. by H1, ..., Hn done

  ∀-eliminazione + →-eliminazione + ↔-eliminazione + ∧-introduzione + ⊥-eliminazione
  si dimostra la conclusione del teorema combinando assieme le n ipotesi tramite un numero arbitrario di applicazione delle regole elencate subito sopra e ri-spiegate qua sotto
  si può usare "thus" prima di "by" per aggiugere l'ultima ipotesi introdotta, anonima o meno
  la dimostrazione (o la sotto-dimostrazione) è conclusa

  ∀-eliminazione: da un'ipotesi ∀x, P si ottiene P in un caso specifico, ottenuto sostituendo a x qualcosa
    Esempio: da ∀A, ∅ ⊆ A si può ricavare ∅ ⊆ ∅ sostituendo ad A l'insieme vuoto ∅
  →-eliminazione: da un'ipotesi P → Q e da un'ipotesi P si ricava Q
  ↔-eliminazione: da un'ipotesi P ↔ Q si ricava sia P → Q che Q → P
  ∧-introduzione: da un'ipotesi P e da un'ipotesi Q si ricava P ∧ Q
  ⊥-eliminazione: da un'ipotesi False si ricava qualunque cosa

. by H1, ..., Hn we proved P as H

  come il caso precedente, ma invece di dimostrare la conclusione si ricava una nuova ipotesi P alla quale viene data il nome H
  dopo P è possibile specificare "that is equivalent to R" per espandere le definizioni contenute in P
  in tal caso la nuova ipotesi ha la forma R e non più P
  "as H" può essere omesso; in tal caso si può usare l'ipotesi solo al passo successivo con thus
  la conclusione da dimostrare non cambia

. by H1, ..., Hn we proved P as H₁ and Q as H₂

  come il caso precedente, ma invece di concludere P ∧ Q
  si applica un passo di ∧-eliminazione concludendo separatamente
  sia P che Q. Alle due conclusioni vengono date i nomi indicati

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

-- !! Seguite gli esercizi spostando il cursore nei commenti e guardando
-- la finestra sulla destra per capire in che punto della dimostrazione siete !!

------- Laboratorio del 25/09/2024 ----------

-- Esercizio 1: riflessività dell'inclusione
theorem reflexivity_inclusion: ∀A, A ⊆ A := by
  /- Stiamo dimostrando un ∀ quindi dobbiamo introdurlo,
     per dimostrare ∀X,( P ) dobbimo fissare X e dimostrare P
     In questo caso (∀A, A ⊆ A), fissiamo A e passiamo a dimostrare A ⊆ A
  -/
 assume A: set
 we need to prove A ⊆ A that is equivalent to ∀Z, Z ∈ A → Z ∈ A
 /- Definizione di essere sottoinsieme: ∀X,∀Y.(  X⊆Y ↔ (∀Z, Z∈X → Z∈Y)  )
    In questo caso (A ⊆ A) scegliamo X=A e Y=A ed andiamo a sostituire,
    quindi A ⊆ A e' equivalente a ∀Z, Z∈A → Z∈A -/
 assume Z: set --Introduzione di ∀
 /- Ora stiamo dimostrando (Z∈A → Z∈A) che e' un implica, quindi dobbiamo introdurlo
    Per dimostrare P→Q assumiamo P e passiamo a dimostrare Q
    In questo caso assumiamo (Z∈A) e passiamo a dimostrare (Z∈A)
 -/
 suppose Z ∈ A
 /- L'ultima ipotesi afferma che (Z∈A) e dobbiamo dimostrare (Z∈A),
    quindi abbiamo concluso
 -/
 thus done

-- Esercizio 2: transitività dell'inclusione
theorem transitivity_inclusion: ∀A B C, A ⊆ B → B ⊆ C → A ⊆ C := by
 -- Introduciamo gli insiemi A, B, C
 assume A: set
 assume B: set
 assume C: set
 /- Di seguito abbiamo due passaggi combinati,
    dato che stiamo dimostrando (A⊆B → (B⊆C→ A⊆C)) che e' un implica,
    assumiamo (A⊆B) come ipotesi, poi la espandiamo con la definizione di essere sottoinsieme
    per cui abbiamo (∀Z, Z∈A → Z∈B) e chiamiamo questa nuova ipotesi H₁.
    Dopodiche' passiamo a dimostrare (B⊆C→ A⊆C)
 -/
 suppose A ⊆ B that is equivalent to ∀Z, Z∈A → Z∈B as H₁
 --ripetiamo il passaggio per (B⊆C→ A⊆C)
 suppose B⊆C that is equivalent to ∀Z, Z∈B → Z∈C as H₂
 /- Ora ribadiamo cio' che stiamo provando (A⊆C) e lo espandiamo con la definizione di essere sottoinsieme,
    quindi passiamo a dimostrare (∀Z, Z∈A → Z∈C)
 -/
 we need to prove A ⊆ C that is equivalent to ∀Z, Z∈A → Z∈C
 -- Fissiamo Z
 assume Z: set
 -- Stiamo dimostrando (Z∈A → Z∈C) quindi assumiamo Z∈A e dimostriamo Z∈C
 suppose Z∈A
 -- dato che (Z∈A), e H₁ ci dice che (∀Z, Z∈A → Z∈B), allora sappiamo che (Z∈B)
 thus by H₁ we proved Z ∈ B
 -- dato che (Z∈B), e H₂ ci dice che (∀Z, Z∈B → Z∈C), allora (Z∈C),
 -- che quello che vogliamo dimostrare, quindi abbiamo finito
 thus by H₂ done

-- Esercizio 3: due insiemi ognuno sottoinsieme dell'altro sono uguali
theorem subset_to_eq: ∀A B, A ⊆ B → B ⊆ A → A = B := by
 --fissiamo A e B
 assume A: set
 assume B: set
 --Stiamo dimostrando A⊆B → (B⊆A → A=B), quindi assumiamo A⊆B e lo espandiamo
 suppose A⊆B that is equivalent to ∀Z, Z∈A → Z∈B as H₁
 --Stiamo dimostrando (B⊆A → A=B), assumiamo B⊆A e lo espandiamo
 suppose B⊆A that is equivalent to ∀Z, Z∈B → Z∈A as H₂
 -- ribadiamo che stiamo dimostrando A=B  (solo per leggibilita' della prova, utile anche a verificare se abbiamo commesso errori)
 we need to prove A = B
 /- Assioma di estensionalita' ∀X,∀Y,((∀Z, Z∈X ↔ Z∈Y) ↔ X=Y)
    In questo caso ci interessa solo in una direzione ∀X,∀Y,((∀Z, Z∈X ↔ Z∈Y) → X=Y)
    !! Nota : se stiamo dimosrando Q e sappiamo che (P→Q), possiamo ridurci a dimostrare P !!
    Poiche' stiamo dimostrando A=B, per l'assioma di estensionalita' (scegliendo X=A e Y=B),
    possiamo ridurci a dimostrare (∀Z, Z∈A ↔ Z∈B)
 -/
 by ax_extensionality1 it suffices to prove ∀Z, Z∈A ↔ Z∈B
 --fissiamo Z
 assume Z: set
 -- Dobbiamo dimostrare Z∈A ↔ Z∈B che e' un "se e solo se",
 -- quindi dobbiamo dimostrare tutte e due le direzioni (Z∈A → Z∈B) e (Z∈B → Z∈A)
 we split the proof
 . we need to prove Z∈A → Z∈B
   -- Stiamo dimostrando (Z∈A → Z∈B), quindi assumiamo Z∈A e dimostriamo Z∈B
   suppose Z∈A
   -- Stiamo dimostrando Z∈B
   -- Dato che Z∈A, e H₁ ci dice che (∀Z, Z∈A → Z∈B), allora sappiamo che Z∈B,
   -- Che e' quello che vogliamo dimostrare, quindi abbiamo finito
   thus by H₁ done
 . we need to prove Z∈B → Z∈A
   -- Stiamo dimostrando Z∈B → Z∈A, assumiamo Z∈B e dimostriamo Z∈A
   suppose Z∈B
   -- Dato che Z∈B, e H₂ ci dice che (∀Z, Z∈B → Z∈A), allora Z∈A
   thus by H₂ done

-- Esercizio 4: insiemi uguali sono sottoinsiemi uno dell'altro
theorem eq_to_subset1: ∀A B, A = B → A ⊆ B := by
 -- Fissiamo A e B
 assume A: set
 assume B: set
 -- Stiamo dimostrando A=B → A⊆B, assumiamo A=B e dimostriamo A⊆B
 suppose A=B
 /- Dato che A=B e l'assioma dell'estensionalita' ci dice che ∀X,∀Y,(X=Y → (∀Z, Z∈X ↔ Z∈Y)),
    allora sappiamo che ∀Z, Z∈A ↔ Z∈B (Scegliendo X=A e Y=B)
 -/
 thus by ax_extensionality2 we proved ∀Z, Z∈A ↔ Z∈B as H
 -- Dobbiamo provare A⊆B che per la definizione di essere sottoinsieme e' uguale a...
 -- Qui abbiamo usato X al posto di Z per non confonderci con le variabili
 -- Una variabile legata dal ∀ possiamo rinominarla con qualsiasi altra variabile,
 -- stando attenti a non catturare una variabile libera, in questo caso A o B non andrebbero bene poiche' libere
 we need to prove A⊆B that is equivalent to ∀X, X∈A → X∈B
 --fissiamo X
 assume X: set
 -- Stiamo dimostrando X∈A → X∈B, assumiamo X∈A e dimostriamo X∈B
 suppose X∈A as K
 -- Dato che H ci dice che (∀Z, Z∈A ↔ Z∈B), vale anche per X (scegliamo Z=X)
 -- quindi sappiamo che X∈A ↔ X∈B, che possimo spezzare come (X∈A → X∈B) e (X∈B → X∈A)
 -- in questo caso ci interessa solo (X∈A → X∈B)
 thus by H we proved X ∈ A → X ∈ B
 -- Dato che (X∈A → X∈B), e K ci dice che X∈A, sappiamo che X∈B, che e' quello che stiamo diostrando
 thus by K done

-- Esercizio 5: insiemi uguali sono sottoinsiemi uno dell'altro
-- Notate la stretta similitudine dell'enunciato con quello della prova precedente: anche le due dimostrazioni si assomiglieranno...
theorem eq_to_subset2: ∀A B, A=B → B⊆A := by
-- Fissiamo A e B
assume A: set
assume B: set
-- Sto dimostrando A=B → B⊆A
suppose A=B
-- Da A=B e estensionalita' sappiamo che ∀W, W∈A ↔ W∈B
-- Ho usato W al posto di Z per far vedere che il nome della variabile puo' essere cambiato
thus by ax_extensionality2 we proved ∀W, W∈A ↔ W∈B as H
-- Espando B⊆A
we need to prove B⊆A that is equivalent to ∀x, x∈B → x∈A
-- Fisso x
assume x: set
-- Sto dimostrando x∈B → x∈A
suppose x∈B as K
-- Da x∈B e H so che (x∈B → x∈A)
thus by H we proved x∈B → x∈A
-- Da (x∈B → x∈A), e K (x∈B), sappiamo che x∈A
thus  by K done

-- Esercizio 6: transitività dell'uguaglianza
-- La dimostrazione viene molto abbreviata se utilizziamo come lemmi tutti i teoremi dimostrati in precedenza
theorem transitivity_equality: ∀(A : set) B C, A=B → B=C → A=C := by
 -- Fissiamo A, B, C
 assume A: set
 assume B: set
 assume C: set
 -- Sto dimostrando A=B → (B=C → A=C), assumo A=B, dimostro (B=C → A=C)
 suppose A=B as H₁
 -- Sto dimostrando (B=C → A=C), assumo B=C, dimostro A=C
 suppose B=C as H₂
 -- Da H₁ (A=B) e il teorema precedentemente dimostrato eq_to_subset1 (∀A,∀B, A=B → A⊆B)
 -- sappiamo che A⊆B
 by eq_to_subset1, H₁ we proved A⊆B as H₁₁
 -- Analogamente da H₁ e eq_to_subset2 (∀A,∀B, A=B → B⊆A), sappiamo che B⊆A
 by eq_to_subset2, H₁ we proved B⊆A as H₁₂
 -- Stessa cosa per H₂ (B=C)
 by eq_to_subset1, H₂ we proved B⊆C as H₂₁
 by eq_to_subset2, H₂ we proved C⊆B as H₂₂

 -- Da H₁₁ (A⊆B), H₂₁ (B⊆A) e il teorema transitivity_inclusion (∀X,Y,W, X⊆Y → Y⊆W→ X⊆W),
 -- sappiamo che A⊆C
 by H₁₁, H₂₁, transitivity_inclusion we proved A⊆C as K₁
 -- Da H₂₂ (C⊆B), H₁₂ (B⊆A) e transitivity_inclusion, sappiamo che C⊆A
 by H₂₂, H₁₂, transitivity_inclusion we proved C⊆A as K₂
 -- Dato che A⊆C (K₁) e C⊆A (K₂), il teorema subset_to_eq ci dice che A=C, quindi fatto
 by subset_to_eq, K₁, K₂ done

------- Laboratorio del 02/10/2024 ----------

-- Esercizio 7: l'insieme vuoto è sottoinsieme di ogni insieme
-- Notate che, poichè ⊆ è solo una definizione, l'enunciato si espande a
--    ∀A X, X ∈ ∅ → X ∈ A
-- e potete usare il teorema come lemma come se fosse scritto in forma espansa
theorem emptyset_is_subset: ∀A, ∅ ⊆ A := by
 assume …
 we need to prove … that is equivalent to ∀X, …
 assume X : set
 suppose …
 thus by … we proved False
 thus done  -- Qui state applicando la regola di eliminazione del False/bottom

-- non cancellare la seguente riga, utile per la correzione automatica
#check emptyset_is_subset



-- Esercizio 8: idempotenza dell'intersezione
theorem intersection_idempotent: ∀A, A ∩ A = A := by
 assume A : set
 by ax_extensionality1 it suffices to prove ∀Z, …
 assume Z : set
 we split the proof
 . we need to prove …
   suppose …
   thus by ax_intersect1 we proved Z ∈ A as H₁ and Z ∈ A as H₂ -- qui uso l'∧-eliminazione
   thus done
 . we need to prove Z ∈ A → Z ∈ A ∩ A
   suppose Z ∈ A
   thus by ax_intersect2 done -- qui viene usata l'∧-introduzione. Sapete dire perchè? In caso contrario esplicitate i passaggi intermedi per capirlo

-- non cancellare la seguente riga, utile per la correzione automatica
#check intersection_idempotent



-- Esercizio 9: il vuoto è l'elemento assorbente dell'intersezione
theorem intersect_empty: ∀A, A ∩ ∅ = ∅ := by
 assume …
 by … it suffices to prove …
 assume …
 we split the proof
 . …
 . suppose Z ∈ ∅
   thus by … done -- quale lemma dimostrato in precedenza devo invocare qui?

-- non cancellare la seguente riga, utile per la correzione automatica
#check intersect_empty



-- Esercizio 10: l'unico sottoinsieme dell'insieme vuoto è l'insieme vuoto
theorem subseteq_emptyset: ∀X, X ⊆ ∅ → X = ∅ := by
 assume X: set
 suppose X ⊆ ∅
 thus by … done -- quali lemmi dimostrati in precedenza devo invocare qui?

-- non cancellare la seguente riga, utile per la correzione automatica
#check subseteq_emptyset



-- Esercizio 11: lemma per dimostrare che l'intersezione è commutativa
theorem intersect_commutative_aux: ∀A B, A ∩ B ⊆ B ∩ A := by
 …

-- non cancellare la seguente riga, utile per la correzione automatica
#check intersect_commutative_aux




-- Esercizio 12: l'intersezione è commutativa
theorem intersect_commutative: ∀A B, A ∩ B = B ∩ A := by
 assume A : set
 assume B : set
 by … done -- quali lemmi dimostrati in precedenza devo invocare qui?

-- non cancellare la seguente riga, utile per la correzione automatica
#check intersect_commutative



-- Esercizio 13: l'intersezione è bi-monotona
theorem intersect_monotone: ∀A B A' B', A ⊆ A' → B ⊆ B' → A ∩ B ⊆ A' ∩ B' := by
 assume A : set
 …
 suppose A ⊆ A' that is equivalent to ∀Z, Z ∈ A → Z ∈ A' as H₁
 …
 we need to prove … that is equivalent to ∀W, W ∈ A ∩ B → W ∈ A' ∩ B'
 assume W : set
 suppose W ∈ A ∩ B
 thus by … we proved W ∈ A as K₁ and … as K₂
 by … we proved W ∈ A' as L₁
 by … we proved W ∈ B' as L₂
 by … done -- completate con le ipotesi e gli assiomi necessari; ricordate che la ∧-introduzione viene usata automaticamente dal "by"

-- non cancellare la seguente riga, utile per la correzione automatica
#check intersect_monotone



-- Esercizio 14: l'intersezione è un sottoinsieme
theorem intersect_is_subset: ∀A B, A ∩ B ⊆ A := by
 …

-- non cancellare la seguente riga, utile per la correzione automatica
#check intersect_is_subset

end set_theory
