------------------------------ MODULE walletv3 ------------------------------
EXTENDS Naturals
VARIABLES vouc1_p, vouc1_n, (*bal_p,*) bal_n, vec_clc
CONSTANTS Replicas, V1_buy_limit, V1_use_limit, Qty_limit, Vec_clc_limit(*, Bal_p_limit*), Bal_n_limit, Init_bal, Vouc1_cost

-----------------------------------------------------------------------------

TypeInv == /\ vouc1_p \in [Replicas -> [Replicas->0..V1_buy_limit]]
           /\ vouc1_n \in [Replicas -> [Replicas->0..V1_use_limit]]
          \* /\ bal_p \in [Replicas -> [Replicas->0..Bal_p_limit]]
           /\ bal_n \in [Replicas -> [Replicas->0..Bal_n_limit]]
           /\ vec_clc \in [Replicas -> [Replicas->0..Vec_clc_limit]]

(*LOCAL SumAll(f) ==
  LET DSum[S \in SUBSET DOMAIN f] == LET elt == CHOOSE e \in S : TRUE
                                     IN  IF S = {} 
                                           THEN 0
                                           ELSE f[elt] + DSum[S \ {elt}]
  IN  DSum[DOMAIN f]
    
Consistency == /\ \A r \in Replicas: SumAll(vouc1_p[r])*Vouc1_cost = SumAll(bal_n[r])*)

Init == /\ TypeInv
        \*/\ Consistency
        /\ vouc1_p = [r \in Replicas |-> [r2 \in Replicas |-> 0 ]]
        /\ vouc1_n = [r \in Replicas |-> [r2 \in Replicas |-> 0 ]]
        \*/\ bal_p = [r \in Replicas |-> [r2 \in Replicas |-> 0 ]]
        /\ bal_n = [r \in Replicas |-> [r2 \in Replicas |-> 0 ]]
        /\ vec_clc = [r \in Replicas |-> [r2 \in Replicas |-> 0 ]]
      
BuyV1(rep, qty) ==
    LET v1p == vouc1_p[rep]
        new_v1p == [v1p EXCEPT ! [rep] = v1p[rep]+qty]
        b_n == bal_n[rep]
        new_bal_n == [b_n EXCEPT ! [rep] = b_n[rep]+ qty*Vouc1_cost]
        vc == vec_clc[rep]
        new_vc == [vc EXCEPT ! [rep] = vc[rep]+1]

    IN /\ v1p[rep]+qty <= V1_buy_limit
       /\ b_n[rep]+ qty*Vouc1_cost <= Bal_n_limit
       /\ vc[rep]+1 <= Vec_clc_limit
       /\ vouc1_p' = [vouc1_p EXCEPT ! [rep] = new_v1p]
       /\ bal_n' = [bal_n EXCEPT ! [rep] = new_bal_n]
       /\ vec_clc' = [vec_clc EXCEPT ! [rep] = new_vc]
       /\ UNCHANGED vouc1_n
      \* /\ UNCHANGED bal_p
       
UseV1(rep, qty) ==
    LET v1n == vouc1_n[rep]
        new_v1n == [v1n EXCEPT ! [rep] = v1n[rep]+qty]
        vc == vec_clc[rep]
        new_vc == [vc EXCEPT ! [rep] = vc[rep]+1]

    IN /\ v1n[rep]+qty <= V1_use_limit
       /\ vc[rep]+1 <= Vec_clc_limit
       /\ vouc1_n' = [vouc1_n EXCEPT ! [rep] = new_v1n]
       /\ vec_clc' = [vec_clc EXCEPT ! [rep] = new_vc]
       /\ UNCHANGED vouc1_p
       \*/\ UNCHANGED bal_p
       /\ UNCHANGED bal_n

Max(n1, n2) == IF n1> n2 THEN n1 ELSE n2

Merge(r1, r2) ==
    LET vouc1p == vouc1_p[r1]
        vouc2p == vouc1_p[r2]
        new_vouc1p == [r \in Replicas |-> Max(vouc1p[r], vouc2p[r])]
        vouc1n == vouc1_n[r1]
        vouc2n == vouc1_n[r2]
        new_vouc1n == [r \in Replicas |-> Max(vouc1n[r], vouc2n[r])]
        (*bal_p1 == bal_p[r1]
        bal_p2 == bal_p[r2]
        new_bal_p1 == [r \in Replicas |-> Max(bal_p1[r], bal_p2[r])]*)
        bal_n1 == bal_n[r1]
        bal_n2 == bal_n[r2]
        new_bal_n1 == [r \in Replicas |-> Max(bal_n1[r], bal_n2[r])]
        vc1 == vec_clc[r1]
        vc2 == vec_clc[r2]
        new_vc1 == [r \in Replicas |-> Max(vc1[r], vc2[r])]
    IN /\ \E r \in Replicas: vc2[r] > vc1[r]
       /\ vouc1_p' = [vouc1_p EXCEPT ! [r1] = new_vouc1p]
       /\ vouc1_n' = [vouc1_n EXCEPT ! [r1] = new_vouc1n]
       \*/\ bal_p' = [bal_p EXCEPT ! [r1] = new_bal_p1]
       /\ bal_n' = [bal_n EXCEPT ! [r1] = new_bal_n1]
       /\ vec_clc' = [vec_clc EXCEPT ! [r1] = new_vc1]
       
Next == \E r1 \in Replicas, r2 \in Replicas, qty \in 1..Qty_limit: 
                (BuyV1(r1, qty) \/ UseV1(r1,qty) \/ Merge(r1,r2) )

Spec == Init /\ [] [Next]_<<vouc1_p, vouc1_n, (*bal_p,*) bal_n, vec_clc>>

THEOREM Spec => TypeInv\* /\ Consistency

=============================================================================
\* Modification History
\* Last modified Tue Sep 09 05:44:22 EEST 2014 by Suha
\* Created Tue Sep 09 01:52:35 EEST 2014 by Suha
