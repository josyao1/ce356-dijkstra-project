--------------------------- MODULE Dijkstra ---------------------------
EXTENDS Integers, FiniteSets, TLAPS, NaturalsInduction

CONSTANTS N, K
VARIABLES x

ASSUME NAssump == N \in Nat /\ N >= 1
ASSUME KAssump == K \in Nat /\ K >= 2

Init          == x \in [0..N -> 0..K-1]
Priv0         == x[0] = x[N]
PrivI(i)      == x[i] # x[i-1]
Privileged(i) == IF i = 0 THEN Priv0 ELSE PrivI(i)
NumPrivileged == Cardinality({i \in 0..N : Privileged(i)})
Legitimate    == NumPrivileged = 1
AtLeastOnePrivileged == NumPrivileged >= 1
Act0          == x' = [x EXCEPT ![0] = (x[0] + 1) % K]
ActI(i)       == x' = [x EXCEPT ![i] = x[i-1]]
Next          == \/ /\ Priv0 /\ Act0
                 \/ \E i \in 1..N : /\ PrivI(i) /\ ActI(i)
Spec          == Init /\ [][Next]_x
FairSpec      == Spec /\ WF_x(Next)
SelfStabilization == <>[]Legitimate

(* ================================================================== *)
(* HELPER 1                                                           *)
(* If no process has a "pivot" (x[i] # x[i-1]) then all values       *)
(* are equal, so x[0] = x[N].  Used to contradict ~Priv0 when the    *)
(* chain is flat.                                                     *)
(* Fix: explicit arithmetic steps for j ∈ 0..N-1 and j+1 ∈ 1..N    *)
(* before using the chain assumption; Isa closes the arithmetic.      *)
(* ================================================================== *)
LEMMA NoPivotImpliesAllEqual ==
  ASSUME NEW f \in [0..N -> 0..K-1],
         \A i \in 1..N : f[i] = f[i-1]
  PROVE  f[0] = f[N]
<1> DEFINE P(j) == j \in 0..N => f[j] = f[0]
<1>1. P(0)
      BY DEF P
<1>2. \A j \in Nat : P(j) => P(j+1)
  <2> TAKE j \in Nat
  <2> ASSUME P(j) PROVE P(j+1)
  <2>1. SUFFICES ASSUME j+1 \in 0..N PROVE f[j+1] = f[0]
        BY DEF P
  <2>2. j \in 0..N-1
        BY <2>1, NAssump, Isa
  <2>3. j+1 \in 1..N
        BY <2>2, NAssump, Isa
  <2>4. f[j+1] = f[j]
        BY <2>3, Isa
        (* outer \A i \in 1..N instantiated at i=j+1; Isa simplifies j+1-1=j *)
  <2>5. j \in 0..N
        BY <2>2, NAssump, Isa
  <2>6. f[j] = f[0]
        BY <2>5 DEF P
  <2>q. QED BY <2>4, <2>6
<1>3. \A j \in Nat : P(j)
      BY <1>1, <1>2, NatInduction, Isa
<1>q. QED BY <1>3, NAssump DEF P

(* ================================================================== *)
(* HELPER 2  (Fix B — no FiniteSetsTheorems)                         *)
(* Every non-empty subset of 0..N has cardinality ≥ 1.               *)
(* All FS_* names replaced with raw Isa: the Isabelle backend has     *)
(* built-in TLA+ finite-set knowledge (intervals, singletons,         *)
(* subset monotonicity) that it can apply without named lemmas.       *)
(* ================================================================== *)
LEMMA CardGe1 ==
  ASSUME NEW S \in SUBSET (0..N),
         S # {}
  PROVE  Cardinality(S) >= 1
<1>1. IsFiniteSet(0..N)
      BY NAssump, Isa
<1>2. IsFiniteSet(S)
      BY <1>1, Isa
<1>3. Cardinality(S) \in Nat
      BY <1>2, Isa
<1>4. \E e \in 0..N : e \in S
      BY Isa
<1>5. PICK e \in 0..N : e \in S
      BY <1>4
<1>6. {e} \subseteq S
      BY <1>5
<1>7. IsFiniteSet({e})
      BY Isa
<1>8. Cardinality({e}) = 1
      BY Isa
<1>9. Cardinality({e}) <= Cardinality(S)
      BY <1>2, <1>6, <1>7, Isa
<1>q. QED BY <1>3, <1>8, <1>9

(* ================================================================== *)
(* MAIN THEOREM                                                       *)
(* We prove the combined invariant                                    *)
(*   Inv ≜ TypeOK ∧ AtLeastOnePrivileged                             *)
(* so that the consecution step has  x ∈ [0..N→0..K-1]  available   *)
(* when type-checking x' (EXCEPT) and applying NoPivotImpliesAllEqual *)
(* to x'.  AtLeastOnePrivileged then follows from []Inv.             *)
(* ================================================================== *)
THEOREM AtLeastOnePrivilegedInvariant ==
    Spec => []AtLeastOnePrivileged
<1> DEFINE TypeOK == x \in [0..N -> 0..K-1]
<1> DEFINE Inv    == TypeOK /\ AtLeastOnePrivileged

(* ------------------------------------------------------------------ *)
(* Base case: Init => Inv                                             *)
(* ------------------------------------------------------------------ *)
<1>1. Init => Inv
  <2>1. SUFFICES ASSUME Init PROVE Inv
        OBVIOUS
  <2>2. TypeOK
        BY DEF Init, TypeOK
  <2>3. AtLeastOnePrivileged
    <3>1. CASE Priv0
      <4>1. Privileged(0)
            BY <3>1 DEF Privileged, Priv0
      <4>2. 0 \in {i \in 0..N : Privileged(i)}
            BY <4>1, NAssump
      <4>3. {i \in 0..N : Privileged(i)} # {}
            BY <4>2
      <4>q. QED BY <4>3, CardGe1 DEF AtLeastOnePrivileged, NumPrivileged
    <3>2. CASE ~Priv0
      <4>1. ~(\A i \in 1..N : x[i] = x[i-1])
        <5>1. ASSUME \A i \in 1..N : x[i] = x[i-1] PROVE FALSE
              BY <5>1, <2>2, <3>2, NoPivotImpliesAllEqual DEF Priv0, TypeOK
        <5>q. QED BY <5>1
      <4>2. \E i \in 1..N : Privileged(i)
            BY <4>1 DEF Privileged, PrivI
      <4>3. \E i \in 0..N : Privileged(i)
            BY <4>2, NAssump, Isa
      <4>4. {i \in 0..N : Privileged(i)} # {}
            BY <4>3
      <4>q. QED BY <4>4, CardGe1 DEF AtLeastOnePrivileged, NumPrivileged
    <3>q. QED BY <3>1, <3>2
  <2>q. QED BY <2>2, <2>3 DEF Inv

(* ------------------------------------------------------------------ *)
(* Consecution step: Inv /\ [Next]_x => Inv'                         *)
(* ------------------------------------------------------------------ *)
<1>2. Inv /\ [Next]_x => Inv'
  <2>s. SUFFICES ASSUME Inv, [Next]_x PROVE Inv'
        OBVIOUS
  <2>0. x \in [0..N -> 0..K-1]
        BY DEF Inv, TypeOK

  (* Stuttering: everything primed = unprimed, Inv' = Inv *)
  <2>1. CASE x' = x
        BY <2>1, <2>0 DEF Inv, TypeOK, AtLeastOnePrivileged,
                         NumPrivileged, Privileged, Priv0, PrivI

  <2>2. CASE Next

    (* Part A: type invariant is preserved *)
    <3>1. TypeOK'
      <4>1. CASE Priv0 /\ Act0
        <5>1. x' = [x EXCEPT ![0] = (x[0]+1) % K]
              BY <4>1 DEF Act0
        <5>2. x[0] \in 0..K-1
              BY <2>0, NAssump DEF TypeOK
        <5>3. (x[0]+1) % K \in 0..K-1
              BY <5>2, KAssump, Isa
        <5>q. QED BY <5>1, <5>3, <2>0, NAssump, Isa DEF TypeOK
      <4>2. CASE \E i \in 1..N : PrivI(i) /\ ActI(i)
        <5>1. PICK i \in 1..N : PrivI(i) /\ ActI(i)
              BY <4>2
        <5>2. x' = [x EXCEPT ![i] = x[i-1]]
              BY <5>1 DEF ActI
        <5>3. i-1 \in 0..N
              BY <5>1, NAssump, Isa
        <5>4. x[i-1] \in 0..K-1
              BY <5>3, <2>0 DEF TypeOK
        <5>q. QED BY <5>2, <5>4, <2>0, NAssump, Isa DEF TypeOK
      <4>q. QED BY <4>1, <4>2, <2>2 DEF Next, Priv0, PrivI

    (* Part B: at-least-one-privileged is preserved *)
    <3>2. AtLeastOnePrivileged'
      <4>0. x' \in [0..N -> 0..K-1]
            BY <3>1 DEF TypeOK

      (* Sub-case: process 0 is privileged in the primed state *)
      <4>1. CASE x'[0] = x'[N]
        <5>1. 0 \in {i \in 0..N : Privileged(i)'}
              BY <4>1, NAssump DEF Privileged, Priv0
        <5>2. {i \in 0..N : Privileged(i)'} # {}
              BY <5>1
        <5>q. QED BY <5>2, CardGe1 DEF AtLeastOnePrivileged, NumPrivileged

      (* Sub-case: x'[0] ≠ x'[N], so the chain cannot be flat *)
      <4>2. CASE x'[0] # x'[N]
        <5>1. ~(\A i \in 1..N : x'[i] = x'[i-1])
          <6>1. ASSUME \A i \in 1..N : x'[i] = x'[i-1] PROVE FALSE
                BY <6>1, <4>0, <4>2, NoPivotImpliesAllEqual
          <6>q. QED BY <6>1
        <5>2. \E i \in 0..N : Privileged(i)'
              BY <5>1, NAssump, Isa DEF Privileged, PrivI
        <5>3. {i \in 0..N : Privileged(i)'} # {}
              BY <5>2
        <5>q. QED BY <5>3, CardGe1 DEF AtLeastOnePrivileged, NumPrivileged

      <4>q. QED BY <4>1, <4>2

    <3>q. QED BY <3>1, <3>2 DEF Inv, TypeOK

  <2>q. QED BY <2>1, <2>2

(* ------------------------------------------------------------------ *)
(* Temporal: []Inv => []AtLeastOnePrivileged, then combine            *)
(* ------------------------------------------------------------------ *)
<1>3. []Inv => []AtLeastOnePrivileged
      BY PTL DEF Inv

<1>q. QED BY <1>1, <1>2, <1>3, PTL DEF Spec

=============================================================================