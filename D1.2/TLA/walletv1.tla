------------------------------ MODULE walletv1 ------------------------------
EXTENDS Reals, Naturals, Sequences
VARIABLES wallets
CONSTANTS Replicas, Voucher1, Voucher2, InitBal

------------------------------------------------------------------------------

\* PN Counter record for Naturals
PNInt == [ p: [Replicas->Nat],
           n: [Replicas->Nat]]
 
\* PN Counter record for Reals
PNReal == [p: [Replicas->Real],
           n: [Replicas->Real]]
           
\* Vouchers do not contain ID since we assume 2 voucher types for now and we have separate fields for each of them in wallets           
Voucher == [cost: Real,
            count: PNInt]

\* Vector clock record used for synchronization purposes. After an explicit operation (buying or selling a voucher) performed on a replica r1,
\* r1th position of vector clock of r1 is incremented by one. Synchronization or communication operations (like DoMerge) do not cause its own
\* index of vector clock of this replica to increase. Otherwise DoMerge operation becomes divergent with redundant new states.
VecClock == [Replicas -> Nat]

\* Record for wallet representation. This record is also  used for representing the local state of the replica, since we assume one customer for simplicity.
Wallet == [balance: PNReal,
          v1: Voucher,
          v2: Voucher,
          vc: VecClock]

\* Invariants determining the types of variables and constants
TypeInvariant == /\ wallets \in [Replicas -> Seq(Wallet)]
                 /\ Voucher1 \in Voucher
                 /\ Voucher2 \in Voucher
                 /\ InitBal \in Real

\* Initial state of the replicas. All values are 0 except the initial balance of the client.    
Init == /\ TypeInvariant 
        /\ wallets = [r \in Replicas |-> <<[balance: [p: [rep \in Replicas |-> InitBal], n: [rep \in Replicas |-> 0]],
                                          v1: [cost: Voucher1.cost, count: [p: [rep \in Replicas |-> 0], n: [rep \in Replicas |-> 0]]],
                                          v2: [cost: Voucher2.cost, count: [p: [rep \in Replicas |-> 0], n: [rep \in Replicas |-> 0]]],
                                          vc: [r2 \in Replicas |-> 0]
                                          ]>>]
\* An operator for summing all the elements in the range of a function map:Replicas->Nat or Real
SumAll(map) ==
    LET Sum[r \in SUBSET Replicas] == IF r ={} THEN 0 ELSE LET x == {CHOOSE x: x \in r} IN map[x]+ Sum[r\x]
    IN Sum[Replicas]

\*Alternative to sum all in case above one does not work
 Sum2[r \in SUBSET Replicas, map \in [Replicas -> Nat]] == IF r ={} THEN 0 ELSE LET x == {CHOOSE x: x \in r} IN map[x]+ Sum2[r\x]
\* Function for buying qty amount of Voucher 1 using the replica atReplica:
\* PreCond: Wallet should contain at least qty*Voucher1.cost balance.   
\* PostCond: -Wallet's balance decrements by qty*Voucher1.cost
\*           -Voucher 1's count increments by qty
\*           -'atReplica'th index of the vector clock is incremented by one.                                  
BuyVoucherOne(atReplica, qty) == 
    LET wr == Tail(wallets[atReplica])
        newBal_p == wr.balance.p
        newBal_n == [wr.balance.n EXCEPT ! [atReplica] = wr.balance.n[atReplica]+qty*Voucher1.cost]
        newBal == [p |-> newBal_p, n |-> newBal_n]
        newv1_cnt_p == [wr.v1.count.p EXCEPT ! [atReplica] = wr.v1.count.p[atReplica]+qty]
        newv1_cnt == [p |-> newv1_cnt_p, n |-> wr.v1.n]
        newv1 == [cost |-> Voucher1.cost, count |-> newv1_cnt]
        newvc == [wr.vc EXCEPT ! [atReplica] = wr.vc[atReplica]+1 ]
        wrNew == [ balance |-> newBal,
                   v1 |-> newv1,
                   v2 |-> wr.v2,
                   vc |-> newvc]
    IN /\ SumAll(wr.balance.p) >= SumAll(wr.balance.n) + qty*Voucher1.cost
       /\ wallets' = [wallets EXCEPT ! [atReplica] = Append(@[atReplica],wrNew)]

\* Function for buying qty amount of Voucher 2 using replica atReplica:
\* PreCond: Wallet should contain at least qty*Voucher2.cost balance.   
\* PostCond: -Wallet's balance decrements by qty*Voucher2.cost
\*           -Voucher 2's count increments by qty
\*           -'atReplica'th index of the vector clock is incremented by one.  
BuyVoucherTwo(atReplica, qty) == 
    LET wr == Tail(wallets[atReplica])
        newBal_p == wr.balance.p
        newBal_n == [wr.balance.n EXCEPT ! [atReplica] = wr.balance.n[atReplica]+qty*Voucher2.cost]
        newBal == [p |-> newBal_p, n |-> newBal_n]
        newv2_cnt_p == [wr.v2.count.p EXCEPT ! [atReplica] = wr.v2.count.p[atReplica]+qty]
        newv2_cnt == [p |-> newv2_cnt_p, n |-> wr.v2.n]
        newv2 == [cost |-> Voucher2.cost, count |-> newv2_cnt]
        newvc == [wr.vc EXCEPT ! [atReplica] = wr.vc[atReplica]+1 ]
        wrNew == [ balance |-> newBal,
                   v1 |-> wr.v1,
                   v2 |-> newv2,
                   vc |-> newvc]
    IN /\ SumAll(wr.balance.p) >= SumAll(wr.balance.n) + qty*Voucher2.cost
       /\ wallets' = [wallets EXCEPT ! [atReplica] = Append(@[atReplica],wrNew)]
       
\* Function for using qty amount of Voucher 1 from replica atReplica:
\* PreCond: Wallet's Voucher 1 count should be at least qty   
\* PostCond: -Wallet's Voucher 1 count decrements by qty
\*           -'atReplica'th index of the vector clock is incremented by one.  
UseVoucherOne(atReplica, qty) == 
    LET wr == Tail(wallets[atReplica])
        newv1_cnt_n == [wr.v1.cnt.n EXCEPT ! [atReplica] = wr.v1.cnt.n[atReplica]+qty]
        newv1_cnt ==[p |-> wr.v1.cnt.p, n |-> newv1_cnt_n]
        newv1 == [cost |-> Voucher1.cost, count |-> newv1_cnt]
        newvc == [wr.vc EXCEPT ! [atReplica] = wr.vc[atReplica]+1 ]
        wrNew == [ balance |-> wr.balance,
                   v1 |-> newv1,
                   v2 |-> wr.v2,
                   vc |-> newvc]
    IN /\ SumAll(wr.v1.cnt.p) >= qty + SumAll(wr.v1.cnt.n)
       /\ wallets' = [wallets EXCEPT ! [atReplica] = Append(@[atReplica],wrNew)]
      
\* Function for using qty amount of Voucher 2 from Replica atReplica:
\* PreCond: Wallet's Voucher 2 count should be at least qty   
\* PostCond: -Wallet's Voucher 2 count decrements by qty
\*           -'atReplica'th index of the vector clock is incremented by one.   
UseVoucherTwo(atReplica, qty) == 
    LET wr == Tail(wallets[atReplica])
        newv2_cnt_n == [wr.v2.cnt.n EXCEPT ! [atReplica] = wr.v2.cnt.n[atReplica]+qty]
        newv2_cnt ==[p |-> wr.v2.cnt.p, n |-> newv2_cnt_n]
        newv2 == [cost |-> Voucher2.cost, count |-> newv2_cnt]
        newvc == [wr.vc EXCEPT ! [atReplica] = wr.vc[atReplica]+1 ]
        wrNew == [ balance |-> wr.balance,
                   v1 |-> wr.v1,
                   v2 |-> newv2,
                   vc |-> newvc]
    IN /\SumAll(wr.v2.cnt.p) >= qty + SumAll(wr.v2.cnt.n)
       /\ wallets' = [wallets EXCEPT ! [atReplica] = Append(@[atReplica],wrNew)]

\* Function for finding maximum of two numerals used by DoMerge (side-effect free)
Max(n1, n2) == IF n1> n2 THEN n1 ELSE n2

\*Function that returns indth element of sequence seq used by DoMerge and some consistency invariants (side-effect free)
GetElt(seq, ind) == Head(SubSeq(seq,ind,ind))

\* Function for merging the last states of rep1 and an intermediate (ith) state of rep2 on rep1
\* PreCond: At the ith stage, Rep2 should have an information that Rep1 does not. More formally, There should exist an index j such that
\*          jth value of vector clock of Rep2 is higher than jth value of vector clock of Rep1.
\* PostCond: -Merged state consists of merging of the balance, v1.cost, v2.cost and vc fields. Fields are merged by pairwise comparing and 
\*          picking the maximum of tuples. Merged wallet is appended to the rep1's history sequence.
DoMerge(rep1 , rep2, i) ==
    LET w1 == Head(wallets[rep1])
        w2 == GetElt(wallets[rep2],i)
        new_bal_p == [r \in Replicas |-> Max(w1.balance.p[r], w2.balance.p[r])]
        new_bal_n == [r \in Replicas |-> Max(w1.balance.n[r], w2.balance.n[r])]
        new_bal == [p |-> new_bal_p, n |-> new_bal_n]
        newv1_p == [r \in Replicas |-> Max(w1.v1.cnt.p[r], w2.v1.cnt.p[r])]
        newv1_n == [r \in Replicas |-> Max(w1.v1.cnt.n[r], w2.v1.cnt.n[r])]
        newv1_cnt == [p |-> newv1_p, n |-> newv1_n]
        v1new == [ cost |-> Voucher1.cost, count |-> newv1_cnt]
        newv2_p == [r \in Replicas |-> Max(w1.v2.cnt.p[r], w2.v2.cnt.p[r])]
        newv2_n == [r \in Replicas |-> Max(w1.v2.cnt.n[r], w2.v2.cnt.n[r])]
        newv2_cnt == [p |-> newv2_p, n |-> newv2_n]
        v2new == [ cost |-> Voucher2.cost, count |-> newv2_cnt]
        vcnew == [r \in Replicas |-> Max(w1.vc[r], w2.vc[r])]
        w1new == [balance |-> new_bal, v1 |-> v1new, v2 |-> v2new, vc |-> vcnew]
    IN  /\ \E r \in Replicas: w1.vc[r] < w2.vc[r]
        /\ wallets' = [wallets EXCEPT ! [rep1] = Append(@[rep1],w1new)]



Consistency == \* Wallets begin with a positive amaount of balance
               /\ InitBal >0 
               \* Vouchers' cost match with the cost of vouchers in the wallets
               /\ \A r \in Replicas: wallets[r].v1.cost = Voucher1.cost /\ wallets[r].v2.cost = Voucher2.cost
               \* Invariants for PN Counters to remain nonnegative
               /\ \A r \in Replicas:  SumAll(wallets[r].balance.p) >= SumAll(wallets[r].balance.n)
               /\ \A r \in Replicas:  SumAll(wallets[r].v1.count.p) >= SumAll(wallets[r].v1.count.n) 
               /\ \A r \in Replicas:  SumAll(wallets[r].v2.count.p) >= SumAll(wallets[r].v2.count.n)
               \* Invariants stating that vector clocks and PN Counters increase monotonically
               /\ \A r \in Replicas, r2 \in Replicas, i \in Nat: (i>0 /\ i<Len(wallets[r2]) ) => GetElt(wallets[r],i).vc[r2] <= GetElt(wallets[r],i+1).vc[r2]
               /\ \A r \in Replicas, r2 \in Replicas, i \in Nat: (i>0 /\ i<Len(wallets[r2]) ) => GetElt(wallets[r],i).balance.p[r2] <= GetElt(wallets[r],i+1).balance.p[r2]
               /\ \A r \in Replicas, r2 \in Replicas, i \in Nat: (i>0 /\ i<Len(wallets[r2]) ) => GetElt(wallets[r],i).balance.n[r2] <= GetElt(wallets[r],i+1).balance.n[r2]
               /\ \A r \in Replicas, r2 \in Replicas, i \in Nat: (i>0 /\ i<Len(wallets[r2]) ) => GetElt(wallets[r],i).v1.count.p[r2] <= GetElt(wallets[r],i+1).v1.count.p[r2]
               /\ \A r \in Replicas, r2 \in Replicas, i \in Nat: (i>0 /\ i<Len(wallets[r2]) ) => GetElt(wallets[r],i).v1.count.n[r2] <= GetElt(wallets[r],i+1).v1.count.n[r2]
               /\ \A r \in Replicas, r2 \in Replicas, i \in Nat: (i>0 /\ i<Len(wallets[r2]) ) => GetElt(wallets[r],i).v2.count.p[r2] <= GetElt(wallets[r],i+1).v2.count.p[r2]
               /\ \A r \in Replicas, r2 \in Replicas, i \in Nat: (i>0 /\ i<Len(wallets[r2]) ) => GetElt(wallets[r],i).v2.count.n[r2] <= GetElt(wallets[r],i+1).v2.count.n[r2]               
  
\* Next state transition           
Next == \E r1 \in Replicas, r2 \in Replicas, qty \in Nat, i \in Nat:
    (BuyVoucherOne(r1, qty) \/ UseVoucherOne(r1,qty) \/ DoMerge(r1,r2,i)) /\ qty>0 /\ i>0 /\ i<=Len(wallets[r2])
-----------------------------------------------------------------------
Spec == Init /\ [] [Next]_<<wallets>>
-----------------------------------------------------------------------
THEOREM Spec => TypeInvariant /\ Consistency
=============================================================================
\* Modification History
\* Last modified Wed Aug 27 15:56:58 EEST 2014 by Suha
\* Created Thu Aug 21 15:26:26 EEST 2014 by Suha
