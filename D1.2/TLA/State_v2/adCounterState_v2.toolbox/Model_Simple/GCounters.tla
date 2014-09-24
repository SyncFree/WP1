------------------------------ MODULE GCounters ------------------------------
LOCAL INSTANCE Naturals

\* GCounter(Replicas) == UNION {[Replicas -> Nat]} 
GCounter(Replicas) == UNION {[Replicas -> Nat]}

GCounterInit(Replicas) == [r \in Replicas |-> 0]

GCounterInc(gc,r) == [gc EXCEPT ![r] = @+1]

GCounterValueAt(gc,r) == gc[r]

Max(x, y) == IF x>y THEN x ELSE y

GCounterMerge(gc1,gc2) == [r \in DOMAIN gc1 |-> Max(gc1[r], gc2[r])]

GCounterValue(gc) ==
    LET sum[p \in gc] ==  
        IF gc\{p} = {} THEN p[2]
        ELSE p[2] + sum[gc\{p}]
    IN sum[gc]

=============================================================================
\* Modification History
\* Last modified Mon Sep 22 12:49:26 WEST 2014 by carlaferreira
\* Created Wed Sep 10 16:17:51 CEST 2014 by carlaferreira
