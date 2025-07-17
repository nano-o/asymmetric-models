--------------------- MODULE AsymmetricReliableBroadcast ---------------------

EXTENDS Asymmetric

CONSTANTS
    V \* set of values that may be broadcast
,   null \* a default value not in V

ASSUME null \notin V

VARIABLES
    bcasterWB \* whether the broadcaster is well-behaved
,   bcasterVal \* value sent by the broadcaster, if it is well-behaved
,   echo
,   ready
,   delivered

(**************************************************************************************)
(* Basic typing invariant:                                                            *)
(**************************************************************************************)
TypeOkay ==
    /\ bcasterWB \in BOOLEAN
    /\ bcasterVal \in V
    /\ \A p \in P :
        /\ echo[p] \in V\cup {null}
        /\ ready[p] \in V\cup {null}
        /\ delivered[p] \in V\cup {null}

(**************************************************************************************)
(* Next we give the correctness properties of RB                                      *)
(**************************************************************************************)

(**************************************************************************************)
(* If the broadcaster is well-behaved and C is a consensus cluster, then              *)
(* eventually all members of C must deliver the broadcaster's value                   *)
(**************************************************************************************)
Validity == \A C \in SUBSET P :
    ConsensusCluster(C) /\ bcasterWB => <>(\A p \in C : delivered[p] = bcasterVal)

(**************************************************************************************)
(* If C is a consensus cluster and a member of C delivers v, then eventually all      *)
(* members of C deliver v                                                             *)
(**************************************************************************************)
Agreement ==
    \A C \in SUBSET P : \A p1,p2 \in C, v \in V :
        ConsensusCluster(C) => []((delivered[p1] = v) => <>(delivered[p2] = v))

(**************************************************************************************)
(* A process delivers at most once                                                    *)
(**************************************************************************************)
DeliverOnce == \A v \in V, p \in P \ B :
    [](delivered[p] = v => [](delivered[p] = v))

Init ==
    /\ bcasterWB \in BOOLEAN
    /\ bcasterVal \in V
    /\ echo = [p \in P |-> null]
    /\ ready = [p \in P |-> null]
    /\ delivered = [p \in P |-> null]

Echo(p, v) ==
    /\ bcasterWB => v = bcasterVal
    /\ echo[p] = null
    /\ echo' = [echo EXCEPT ![p] = v]
    /\ UNCHANGED <<bcasterWB, bcasterVal, ready, delivered>>

Ready(p, v, S, T) ==
    /\ ready[p] = null
    /\  \/  /\ S \in SurvivorSets(p)
            /\ \A q \in S \ B : echo[q] = v
        \/  /\ T \in Blocking(p)
            /\ \A q \in T \ B : ready[q] = v
    /\ ready' = [ready EXCEPT ![p] = v]
    /\ UNCHANGED <<bcasterWB, bcasterVal, echo, delivered>>

Deliver(p, v, S) ==
    /\ S \in SurvivorSets(p)
    /\ \A q \in S \ B : ready[q] = v
    /\ delivered[p] = null
    /\ delivered' = [delivered EXCEPT ![p] = v]
    /\ UNCHANGED <<bcasterWB, bcasterVal, echo, ready>>

Next == \E p \in P, v \in V :
    \/  Echo(p,v)
    \/  \E S \in SurvivorSets(p) : \E T \in Blocking(p) : Ready(p,v,S,T)
    \/  \E S \in SurvivorSets(p) : Deliver(p,v,S)

vars == <<bcasterWB, bcasterVal, echo, ready, delivered>>

Fairness == \A p \in P \ B : \A v \in V :
    /\  WF_vars(Echo(p, v))
    /\  \A S \in SurvivorSets(p) :
        /\  S \cap B = {} => WF_vars(Deliver(p, v, S))
        /\  \A T \in Blocking(p) :
            T \cap B = {} => WF_vars(Ready(p, v, S, T))

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ Fairness

==============================================================================

