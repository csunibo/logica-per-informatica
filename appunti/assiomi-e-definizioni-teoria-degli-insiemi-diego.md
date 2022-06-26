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
  \forall X, \exist Y, \forall Z,(Z \in Y \iff Z \in X \and P(Z))
  $$
  * notazione:
    $$
    Y=\{Z \in X\mid P(Z)\}
    $$
  
* insieme vuoto
  $$
  \exist X, \forall Z,Z \notin X
  $$
  
* unione
  Dato un insieme di insiemi, esiste l'insieme che ne è l'unione
  $$
  \forall F, \exist X, \forall Z,(Z \in X \iff \exist Y,(Y \in F \and Z \in Y))
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
  \emptyset \overset{def}{=} \{X \in Y \mid false\}
  $$
  
* intersezione binaria
  $$
  A \cap B \overset{def}{=}\{ X \in A \mid X \in B \}
  $$

* intersezione
  Dato un insieme di insiemi, esiste l’insieme che ne è
  l’intersezione. 
  $$
  \bigcap F \overset{def}{=} \empty \  se \ F=\empty \\
  \bigcap F \overset{def}{=} \{ X \in A \mid \forall Y,(Y \in F \implies X \in Y) \} \ dove A \in F
  $$
  A è ogni elemento di F
  
* notazione alternativa
    $$
    \bigcap F = \bigcap {_{Y \in F}} Y
    $$

