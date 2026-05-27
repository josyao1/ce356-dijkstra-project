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

(* --- PROOF BEGINS HERE --- *)
LOCAL INSTANCE FiniteSetTheorems

TypeOK == x \in [0..N -> 0..K-1]

LOCAL PrivState(y, i) == IF i = 0 THEN y[0] = y[N] ELSE y[i] # y[i-1]
LOCAL NumPrivState(y) == Cardinality({i \in 0..N : PrivState(y, i)})

LEMMA ChainArg ==
  \A y \in [0..N -> 0..K-1] : y[0] = y[N] \/ \E i \in 1..N : y[i] # y[i-1]
<1>1. TAKE y \in [0..N -> 0..K-1]
<1>2. DEFINE P(m) == (m \in 0..N) => (y[0] = y[m] \/ \E i \in 1..m : y[i] # y[i-1])
<1>3. P(0)
  OBVIOUS
<1>4. \A m \in Nat : P(m) => P(m+1)
  <2>1. TAKE m \in Nat
  <2>2. ASSUME P(m), m+1 \in 0..N
        PROVE  y[0] = y[m+1] \/ \E i \in 1..(m+1) : y[i] # y[i-1]
    <3>1. m \in 0..N
      BY <2>1, <2>2, NAssump, SMT
    <3>2. y[0] = y[m] \/ \E i \in 1..m : y[i] # y[i-1]
      BY <2>2, <3>1
    <3>3. CASE y[0] = y[m]
      <4>1. CASE y[m] = y[m+1]
        <5>1. y[0] = y[m+1] BY <3>3, <4>1
        <5>2. QED BY <5>1
      <4>2. CASE y[m] # y[m+1]
        <5>1. m+1 \in 1..(m+1) BY <2>1, SMT 
        <5>2. y[m+1] # y[(m+1)-1] BY <4>2, <2>1, SMT 
        <5>3. \E i \in 1..(m+1) : y[i] # y[i-1] BY <5>1, <5>2
        <5>4. QED BY <5>3
      <4>3. QED BY <4>1, <4>2
    <3>4. CASE \E i \in 1..m : y[i] # y[i-1]
      <4>1. ASSUME NEW i \in 1..m, y[i] # y[i-1]
            PROVE \E j \in 1..(m+1) : y[j] # y[j-1]
        <5>1. i \in 1..(m+1)
          BY <4>1, <2>1, SMT 
        <5>2. QED 
          BY <5>1, <4>1
      <4>2. QED BY <3>4, <4>1
    <3>5. QED BY <3>2, <3>3, <3>4
  <2>3. QED BY <2>1, <2>2
<1>5. \A m \in Nat : P(m)
  BY <1>3, <1>4, NatInduction, Isa
<1>6. QED
  BY <1>5, NAssump, SMT

LEMMA StateAtLeastOne ==
  \A y \in [0..N -> 0..K-1] : NumPrivState(y) >= 1
<1>1. TAKE y \in [0..N -> 0..K-1]
<1>2. DEFINE S == {i \in 0..N : PrivState(y, i)}
<1>3. y[0] = y[N] \/ \E i \in 1..N : y[i] # y[i-1]
  BY <1>1, ChainArg
<1>4. \E i \in 0..N : i \in S
  <2>1. CASE y[0] = y[N]
    <3>1. 0 \in 0..N BY NAssump, SMT
    <3>2. PrivState(y, 0) BY <2>1 DEF PrivState
    <3>3. 0 \in S BY <3>1, <3>2
    <3>4. QED BY <3>3
  <2>2. CASE \E j \in 1..N : y[j] # y[j-1]
    <3>1. ASSUME NEW j \in 1..N, y[j] # y[j-1]
          PROVE  j \in S
      <4>1. j \in 0..N 
        BY <3>1, SMT
      <4>2. PrivState(y, j) 
        BY <3>1 DEF PrivState
      <4>3. QED 
        BY <4>1, <4>2
    <3>2. QED BY <2>2, <3>1
  <2>3. QED BY <1>3, <2>1, <2>2
<1>5. S \subseteq 0..N
  OBVIOUS
<1>6. IsFiniteSet(0..N)
  BY NAssump, FS_Interval
<1>7. IsFiniteSet(S)
  BY <1>5, <1>6, FS_Subset
<1>8. S # {}
  BY <1>4
<1>9. Cardinality(S) \in Nat
  BY <1>7, FS_CardinalityType
<1>10. Cardinality(S) # 0
  BY <1>7, <1>8, FS_EmptySet
<1>11. QED
  BY <1>9, <1>10, SMT DEF NumPrivState
  
THEOREM AtLeastOnePrivilegedInvariant == Spec => []AtLeastOnePrivileged
<1>1. Init => TypeOK /\ AtLeastOnePrivileged
  <2>1. Init => TypeOK
    BY DEF Init, TypeOK
  <2>2. TypeOK => AtLeastOnePrivileged
    <3>1. ASSUME TypeOK
          PROVE  AtLeastOnePrivileged
      <4>1. x \in [0..N -> 0..K-1] BY <3>1 DEF TypeOK
      <4>2. NumPrivState(x) >= 1 BY <4>1, StateAtLeastOne
      <4>3. {i \in 0..N : Privileged(i)} = {i \in 0..N : PrivState(x, i)}
            BY DEF Privileged, Priv0, PrivI, PrivState
      <4>4. NumPrivileged = NumPrivState(x)
            BY <4>3 DEF NumPrivileged, NumPrivState
      <4>5. QED BY <4>2, <4>4 DEF AtLeastOnePrivileged
    <3>2. QED BY <3>1
  <2>3. QED BY <2>1, <2>2
<1>2. TypeOK /\ AtLeastOnePrivileged /\ [Next]_x => TypeOK' /\ AtLeastOnePrivileged'
  <2>1. ASSUME TypeOK, AtLeastOnePrivileged, [Next]_x
        PROVE  TypeOK' /\ AtLeastOnePrivileged'
    <3>1. TypeOK'
      BY <2>1, NAssump, KAssump DEF TypeOK, Next, Priv0, Act0, PrivI, ActI
    <3>2. AtLeastOnePrivileged'
      <4>1. x' \in [0..N -> 0..K-1] BY <3>1 DEF TypeOK
      <4>2. NumPrivState(x') >= 1 BY <4>1, StateAtLeastOne
      <4>3. {i \in 0..N : Privileged(i)'} = {i \in 0..N : PrivState(x', i)}
            BY DEF Privileged, Priv0, PrivI, PrivState
      <4>4. NumPrivileged' = NumPrivState(x')
            BY <4>3 DEF NumPrivileged, NumPrivState
      <4>5. QED BY <4>2, <4>4 DEF AtLeastOnePrivileged
    <3>3. QED BY <3>1, <3>2
  <2>2. QED BY <2>1
<1>3. QED
  BY <1>1, <1>2, PTL DEF Spec
=======================================================================