## assiomi

* estensionabilità
  Due insiemi sono uguali sse hanno gli stessi elementi.
  
  $$
  \forall X, \forall Y,(X=Y \iff \forall Z.(Z \in X \iff Z \in Y))
  $$
  
* separazione
  Dato un insieme, possiamo formare il sottoinsieme dei suoi
  elementi che soddisfano una proprie
  
  $$
  \forall X, \exists Y, \forall Z,(Z \in Y \iff Z \in X \land P(Z))
  $$
  * notazione:
    
    $$
    Y= \{ Z \in X\mid P(Z) \}
    $$
  
* insieme vuoto
  
  $$
  \exists X, \forall Z,Z \notin X
  $$
  
* unione
  Dato un insieme di insiemi, esiste l'insieme che ne è l'unione
  
  $$
  \forall F, \exists X, \forall Z,(Z \in X \iff \exists Y,(Y \in F \land Z \in Y))
  $$
  * notazione:
  
  $$
  X= \bigcup F \ o \ \bigcup {_{Y \in F}}Y
  $$

## definizioni

* essere sottoinsieme 
  
  $$
  X \subseteq Y \overset{def}{=} \forall Z,(Z \in X \implies Z \in Y)
  $$
  
* insieme vuoto (ridondate)
  
  $$
  \emptyset \overset{def}{=} \{ X \in Y \mid false \}
  $$
  
* intersezione binaria
  
  $$
  A \cap B \overset{def}{=}\{ X \in A \mid X \in B \}
  $$

* intersezione
  Dato un insieme di insiemi, esiste l’insieme che ne è
  l’intersezione. 
  
  $$
  \bigcap F \overset{def}{=} \emptyset \  se \ F=\emptyset 
  $$
  
  $$
  \bigcap F \overset{def}{=} \{ X \in A \mid \forall Y,(Y \in F \implies X \in Y) \} \quad dove\ A \in F
  $$
  
  A è ogni elemento di F
  
* notazione alternativa
    
    $$
    \bigcap F = \bigcap {_{Y \in F}} Y
    $$

