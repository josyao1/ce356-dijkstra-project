--------------------------- MODULE Dijkstra ---------------------------

EXTENDS Integers, FiniteSets

CONSTANTS N, K
VARIABLES x

Init == x \in [0..N -> 0..K-1]

Priv0    == x[0] = x[N]
PrivI(i) == x[i] # x[i-1]

Privileged(i) == IF i = 0 THEN Priv0 ELSE PrivI(i)

NumPrivileged == Cardinality({i \in 0..N : Privileged(i)})

Legitimate == NumPrivileged = 1

Act0    == x' = [x EXCEPT ![0] = (x[0] + 1) % K]
ActI(i) == x' = [x EXCEPT ![i] = x[i-1]]

Next == \/ /\ Priv0
           /\ Act0
        \/ \E i \in 1..N :
           /\ PrivI(i)
           /\ ActI(i)

Spec    == Init /\ [][Next]_x
FairSpec == Spec /\ WF_x(Next)

SelfStabilization == <>[]Legitimate
=======================================================================