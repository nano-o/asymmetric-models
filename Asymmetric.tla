--------------------- MODULE Asymmetric ---------------------

CONSTANTS
    P \* the set of processes
,   FailProneSets \* assigns a set of fail-prone sets to each process
,   B \* the actual set of Byzantine processes

WellFormed == \A p \in P :
    /\ FailProneSets[p] \in SUBSET SUBSET P
    /\ \A F \in FailProneSets[p] : F # {}

ASSUME WellFormed

(**************************************************************************************)
(* The survivor sets of a process are the complements of its fail-prone sets          *)
(**************************************************************************************)
SurvivorSets(p) ==
    {S \in SUBSET P : \E F \in FailProneSets[p] : S = P \ F}

(**************************************************************************************)
(* A set T blocks p when it intersects all its survivor sets                          *)
(**************************************************************************************)
Blocking(p) ==
    {T \in SUBSET P : \A S \in SurvivorSets(p) : S \cap T # {}}

(**************************************************************************************)
(* Two processes p and q satisfy B3 when the intersection of the following sets is    *)
(* never empty: a survivor set of p; a survivor set of q; the union of a survivor     *)
(* set of p and a survivor set of q. Note that this does not depend on B.             *)
(**************************************************************************************)
B3(p, q) ==
    \A Sp1, Sp2 \in SurvivorSets(p) :
    \A Sq1, Sq2 \in SurvivorSets(q) :
    Sp1 \cap Sq1 \cap (Sp2 \union Sq2) # {}

(**************************************************************************************)
(* p is wise when its failure assumptions are satisfied                               *)
(**************************************************************************************)
Wise(p) ==
    /\ p \notin B
    /\ \E F \in FailProneSets[p] : B \subseteq F

(**************************************************************************************)
(* G is a guild when all its members are wise and satisfy B3 pairwise                 *)
(**************************************************************************************)
Guild(G) ==
    /\ G # {}
    /\ \A p \in G : Wise(p)
    /\ \A p,q \in G : B3(p, q)

Intertwined(p, q) ==
    \A Sp \in SurvivorSets(p), Sq \in SurvivorSets(q) :
        (Sp \cap Sq) \ B # {}

(**************************************************************************************)
(* A consensus cluster C is a set that should be able to reach agreement given B      *)
(**************************************************************************************)
ConsensusCluster(C) ==
    /\ C # {}
    /\ \A p \in C : Wise(p)
    /\ \A p,q \in C : Intertwined(p, q)

=============================================================================

