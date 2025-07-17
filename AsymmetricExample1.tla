--------------------- MODULE AsymmetricExample1 ---------------------

CONSTANTS p1, p2, p3, p4, null, V

P == {p1, p2, p3, p4}

SurvivorSetsToFailProneSets(SS) == [p \in P |->
    {F \in SUBSET P : \E S \in SS[p] : F = P \ S}]

FailProneSets == SurvivorSetsToFailProneSets(
    [p \in P |->
        CASE
            p = p1 -> {{p1,p3}}
        []  p = p2 -> {{p2,p3}}
        []  p = p3 -> {{p3,p4},{p3,p2}}
        []  p = p4 -> {{p4,p3},{p4,p2}}])
B == {}

VARIABLES bcasterWB, bcasterVal,   echo ,   ready ,   delivered
INSTANCE AsymmetricReliableBroadcast

\* those assumptions are checked by TLC when it checks this file:
ASSUME WellFormed
G1 == {p1,p2,p3}
G2 == {p3,p4}
ASSUME ConsensusCluster(G1)
ASSUME ConsensusCluster(G2)
ASSUME \neg ConsensusCluster(P)

\* NOTE that {p3,p4} is not a guild:
ASSUME \neg Guild({p3,p4})

\* Since the algorithm solves RB for G1 and G2 and they intersect, it should also solve it for G2 \cup G2:
FullValidity == bcasterWB => <>(\A p \in P : delivered[p] = bcasterVal)
FullAgreement ==
    \A p,q \in P, v \in V : []((delivered[p] = v) => <>(delivered[q] = v))

=====================================================================
