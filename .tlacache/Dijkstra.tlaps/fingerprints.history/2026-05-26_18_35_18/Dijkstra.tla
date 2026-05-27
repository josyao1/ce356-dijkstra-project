--------------------------- MODULE Dijkstra ---------------------------

EXTENDS Integers, FiniteSets, TLAPS, NaturalsInduction

CONSTANTS N, K
VARIABLES x

ASSUME NAssump == N \in Nat /\ N >= 1
ASSUME KAssump == K \in Nat /\ K >= 2

Init == x \in [0..N -> 0..K-1]

Priv0    == x[0] = x[N]
PrivI(i) == x[i] # x[i-1]

Privileged(i) == IF i = 0 THEN Priv0 ELSE PrivI(i)

NumPrivileged == Cardinality({i \in 0..N : Privileged(i)})

Legitimate == NumPrivileged = 1

AtLeastOnePrivileged == NumPrivileged >= 1

Act0    == x' = [x EXCEPT ![0] = (x[0] + 1) % K]
ActI(i) == x' = [x EXCEPT ![i] = x[i-1]]

Next == \/ /\ Priv0
           /\ Act0
        \/ \E i \in 1..N :
           /\ PrivI(i)
           /\ ActI(i)

Spec     == Init /\ [][Next]_x
FairSpec == Spec /\ WF_x(Next)

SelfStabilization == <>[]Legitimate

LEMMA NoPivotImpliesAllEqual ==
  ASSUME NEW f \in [0..N -> 0..K-1],
         \A i \in 1..N : f[i] = f[i-1]
  PROVE f[0] = f[N]
<1> DEFINE P(j) == j \in 0..N => f[j] = f[0]
<1>1. P(0)
      BY DEF P
<1>2. \A j \in Nat : P(j) => P(j+1)
  <2> TAKE j \in Nat
  <2> SUFFICES ASSUME P(j), j+1 \in 0..N PROVE f[j+1] = f[0]
      BY DEF P
  <2>1. j \in 0..N-1 BY DEF P
  <2>2. f[j+1] = f[j] OBVIOUS
  <2>q. QED BY <2>2 DEF P
<1>3. \A j \in Nat : P(j)
      BY <1>1, <1>2, NatInduction, Isa
<1>q. QED BY <1>3, NAssump DEF P

THEOREM AtLeastOnePrivilegedInvariant ==
    Spec => []AtLeastOnePrivileged
<1>1. Init => AtLeastOnePrivileged
  <2> SUFFICES ASSUME Init PROVE AtLeastOnePrivileged
      OBVIOUS
  <2>1. x \in [0..N -> 0..K-1]
        BY DEF Init
  <2>2. CASE Priv0
    <3>1. Privileged(0)
          BY <2>2 DEF Privileged, Priv0
    <3>2. 0 \in {i \in 0..N : Privileged(i)}
          BY <3>1
    <3>q. QED BY <3>2, Isa
          DEF AtLeastOnePrivileged, NumPrivileged
  <2>3. CASE ~Priv0
    <3>1. x[0] # x[N]
          BY <2>3 DEF Priv0
    <3>2. ~(\A i \in 1..N : x[i] = x[i-1])
      <4>1. ASSUME \A i \in 1..N : x[i] = x[i-1] PROVE FALSE
            BY <4>1, <3>1, NoPivotImpliesAllEqual, <2>1
      <4>q. QED BY <4>1
    <3>3. \E i \in 1..N : Privileged(i)
          BY <3>2 DEF Privileged, PrivI
    <3>4. {i \in 0..N : Privileged(i)} # {}
          BY <3>3
    <3>q. QED BY <3>4, Isa
          DEF AtLeastOnePrivileged, NumPrivileged
  <2>q. QED BY <2>2, <2>3
<1>2. AtLeastOnePrivileged /\ [Next]_x => AtLeastOnePrivileged'
  <2> SUFFICES ASSUME [Next]_x
               PROVE AtLeastOnePrivileged => AtLeastOnePrivileged'
               OBVIOUS
  <2>1. CASE x' = x
        BY <2>1 DEF AtLeastOnePrivileged, NumPrivileged,
                    Privileged, Priv0, PrivI
  <2>2. CASE Next
    <3>1. x' \in [0..N -> 0..K-1]
      <4>1. CASE Act0
            BY <4>1 DEF Act0
      <4>2. CASE \E i \in 1..N : PrivI(i) /\ ActI(i)
            BY <4>2 DEF ActI
      <4>q. QED BY <4>1, <4>2, <2>2 DEF Next, Priv0, PrivI
    <3>2. CASE x'[0] = x'[N]
      <4>1. {i \in 0..N : Privileged(i)'} # {}
            BY <3>2 DEF Privileged, Priv0
      <4>q. QED BY <4>1, Isa
            DEF AtLeastOnePrivileged, NumPrivileged
    <3>3. CASE x'[0] # x'[N]
      <4>1. ~(\A i \in 1..N : x'[i] = x'[i-1])
        <5>1. ASSUME \A i \in 1..N : x'[i] = x'[i-1] PROVE FALSE
              BY <5>1, <3>3, NoPivotImpliesAllEqual, <3>1
        <5>q. QED BY <5>1
      <4>2. \E i \in 1..N : Privileged(i)'
            BY <4>1 DEF Privileged, PrivI
      <4>3. {i \in 0..N : Privileged(i)'} # {}
            BY <4>2
      <4>q. QED BY <4>3, Isa
            DEF AtLeastOnePrivileged, NumPrivileged
    <3>q. QED BY <3>2, <3>3
  <2>q. QED BY <2>1, <2>2 DEF Next
<1>q. QED BY <1>1, <1>2, PTL DEF Spec

=======================================================================