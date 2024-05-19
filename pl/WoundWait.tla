---------------------------- MODULE WoundWait ----------------------------
EXTENDS TLC, FiniteSets, Integers, Sequences

CONSTANT txs, locks, actives 
VARIABLE tStat, lStat, lOwn, waitList

--------------------------------------------------------------------------

Vars == <<tStat, lStat, lOwn, waitList>>

TypeOK == 
    /\ \A t \in txs: tStat[t] \in {"f", "l"} 
    /\ \A l1 \in locks: lStat[l1] \in {"f", "l"} 
    /\ \A l2 \in locks: lOwn[l2] \in txs \cup {0}
    /\ waitList \subseteq txs

Init == 
    /\ tStat = [t \in txs |-> "f"] 
    /\ lStat = [l \in locks |-> "f"] 
    /\ lOwn = [l \in locks |-> 0]
    /\ waitList = {}

Min(L) == CHOOSE t \in L : \A ts \in L : t <= ts

SignalWait ==   
    IF waitList # {}
    THEN waitList' = waitList \ {Min(waitList)} 
    ELSE UNCHANGED waitList

Wait(t) == /\ waitList' = waitList \cup {t}

CanAcquire(t,l) == 
    \/  /\ lStat[l] = "f" 
    \/  /\ lStat[l] = "l" 
        /\ lOwn[l] = t

AcquireLock(t,l) == 
    \/  /\ CanAcquire(t,l) 
        /\ lStat' = [lStat EXCEPT ![l] = "l"] 
        /\ lOwn' = [lOwn EXCEPT ![l] = t] 
        /\ tStat' = [tStat EXCEPT ![t] = "l"]
        /\ UNCHANGED waitList   
    \/  /\ lStat[l] = "l"
        /\ lOwn[l] # t
        /\ IF (t < lOwn[l]) 
           THEN /\ lStat' = [lStat EXCEPT ![l] = "l"] 
                /\ lOwn' = [lOwn EXCEPT ![l] = t] 
                /\ tStat' = [tStat EXCEPT ![lOwn[l]] = "f"]
                /\ tStat' = [tStat EXCEPT ![t] = "l"]
                /\ UNCHANGED waitList
           ELSE /\ Wait(t)
                /\ UNCHANGED <<tStat, lStat, lOwn>> 

Commit(t,l) == 
    /\ lOwn[l] = t 
    /\ lOwn' = [lOwn EXCEPT ![l] = 0] 
    /\ lStat' = [lStat EXCEPT ![l] = "f"] 
    /\ tStat' = [tStat EXCEPT ![t] = "f"]
    /\ t' = t + actives
    /\ SignalWait 

Next == 
    \E t \in txs : \E l \in locks: 
        \/ AcquireLock(t,l) 
        \/ Commit(t,l)

Spec == 
    /\ Init
    /\ [][Next]_Vars

FairSpec == 
    Spec /\ \A t1 \in txs, l1 \in locks: 
            WF_Vars(AcquireLock(t1,l1))
         /\ \A t2 \in txs, l2 \in locks: 
            WF_Vars(Commit(t2,l2)) 

DeadLock == waitList # txs

Starvation ==
    /\ \A t1 \in txs, l1 \in locks: 
        []<>(<<AcquireLock(t1,l1)>>_Vars)
    /\ \A t2 \in txs, l2 \in locks: 
        []<>(<<Commit(t2,l2)>>_Vars)
============================================================================= 