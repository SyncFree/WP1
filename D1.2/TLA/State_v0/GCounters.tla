------------------------------ MODULE GCounters ------------------------------
LOCAL INSTANCE Naturals
  
GCounter(Replicas) == UNION {[Replicas -> Nat]}

GCounterInit(Replicas) == [r \in Replicas |-> 0]

GCounterInc(gc,r) == [gc EXCEPT ![r] = @+1]

GCounterValueAt(gc,r) == gc[r]

Max(x, y) == IF x>y THEN x ELSE y

GCounterMerge(gc1,gc2) == [r \in DOMAIN gc1 |-> Max(gc1[r], gc2[r])]

GCounterValue(gc) ==     
    LET value[r \in gc] ==
        IF gc\{r} = {} THEN r[2] ELSE r[2] + value[gc\{r}]
    IN value[gc]

=============================================================================
\* Modification History
\* Last modified Sat Sep 13 08:10:30 WEST 2014 by carlaferreira
\* Created Wed Sep 10 16:17:51 CEST 2014 by carlaferreira
