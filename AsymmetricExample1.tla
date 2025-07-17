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
ASSUME ConsensusCluster({p1,p2,p3})
ASSUME ConsensusCluster({p3,p4})
ASSUME \neg ConsensusCluster(P)

\* NOTE:
ASSUME \neg Guild({p3,p4})

=====================================================================
