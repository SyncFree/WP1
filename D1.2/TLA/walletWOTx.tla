----------------------------- MODULE walletWOTx -----------------------------
EXTENDS Naturals, TLC
VARIABLES wallets
CONSTANTS Replicas, V1Cost, InitBal, Natlim, Qtylim

ASSUME /\ V1Cost \in Nat
       /\ InitBal \in Nat
       /\ Natlim \in Nat
       /\ Qtylim \in Nat
       /\ V1Cost > 0
       /\ Natlim > 0
       /\ Qtylim > 0
-----------------------------------------------------------------------------

PNCounter(dom) == [p: [dom -> Nat],
                   n: [dom -> Nat]]
              
InitPNCounter(dom) == [p |-> [d \in dom |-> 0], n |-> [d \in dom |-> 0] ]

   
SumAll(map) ==
    LET Sum[r \in SUBSET DOMAIN map] == IF r ={} THEN 0 ELSE LET y == CHOOSE x \in r: TRUE IN map[y]+ Sum[r\{y}]
    IN Sum[DOMAIN map]
    
EvalPNCounter(pnc) == SumAll(pnc.p) - SumAll(pnc.n) 

Max(n1,n2) == IF n1>= n2 THEN n1 ELSE n2

MergePNCounters(pnc1, pnc2) == [p |-> [d \in DOMAIN pnc1.p |-> Max(pnc1.p[d], pnc2.p[d])], n|-> [d \in DOMAIN pnc1.n |-> Max(pnc1.n[d], pnc2.n[d])] ]
    
-----------------------------------------------------------------------------

Wallet == [balance: PNCounter(Replicas),
           v1cnt: PNCounter(Replicas),
           vecclc: [Replicas ->Nat] ]
           

TypeInv == /\ wallets \in [Replicas->Wallet]


Init == \*/\ Print ("a", TRUE)
        /\ wallets = [r \in Replicas |-> [balance |-> InitPNCounter(Replicas),
                                           v1cnt  |-> InitPNCounter(Replicas),
                                           vecclc |-> [r2 \in Replicas |-> 0] ]]

BuyV1(rep, qty) ==
    LET wr == wallets[rep]
        new_bal_n == [wr.balance.n EXCEPT ! [rep] = wr.balance.n[rep] + qty*V1Cost]
        new_v1_cnt_p == [wr.v1cnt.p EXCEPT ! [rep] = wr.v1cnt.p[rep] + qty]
        new_vc == [wr.vecclc EXCEPT ! [rep] = wr.vecclc[rep]+1]
        wr_new == [balance |-> [p |-> wr.balance.p, n |-> new_bal_n ],
                   v1cnt |-> [p |-> new_v1_cnt_p, n |-> wr.v1cnt.n],
                   vecclc |-> new_vc]
    IN /\ wr.balance.n[rep]+qty*V1Cost <= Natlim
       /\ wr.v1cnt.p[rep]+qty <= Natlim
       /\ wr.vecclc[rep]+1 <= Natlim
       /\ EvalPNCounter(wr.balance)+ InitBal >= qty*V1Cost
       /\ wallets' = [wallets EXCEPT ! [rep] = wr_new ]
       /\ Print("Buy", TRUE)
      \* /\ Print(wallets', TRUE)

Merge(rep1, rep2) ==
    LET wr1 == wallets[rep1]
        wr2 == wallets[rep2]
        new_vc == [r \in Replicas |-> Max(wr1.vecclc[r],wr2.vecclc[r])]
        wr1_new ==[balance |-> MergePNCounters(wr1.balance, wr2.balance),
                   v1cnt |-> MergePNCounters(wr1.v1cnt, wr2.v1cnt),
                   vecclc |-> new_vc]
    IN /\ \E r \in Replicas: wr1.vecclc[r] < wr2.vecclc[r]
       /\ wallets' = [wallets EXCEPT ! [rep1] = wr1_new]
       /\ Print("MergeLastStates", TRUE)
       \*/\ Print(wallets', TRUE)
       
MergeBalance(rep1, rep2) ==
    LET wr1 == wallets[rep1]
        wr2 == wallets[rep2]
        new_vc == [r \in Replicas |-> Max(wr1.vecclc[r],wr2.vecclc[r])]
        wr1_new ==[balance |-> MergePNCounters(wr1.balance, wr2.balance),
                   v1cnt |-> wr1.v1cnt,
                   vecclc |-> new_vc]
    IN /\ \E r \in Replicas: wr1.balance.n[r] < wr2.balance.n[r]
       /\ wallets' = [wallets EXCEPT ! [rep1] = wr1_new]
       /\ Print("MergeBalance", TRUE)
       \*/\ Print(wallets', TRUE)
       
MergeCount(rep1, rep2) ==
    LET wr1 == wallets[rep1]
        wr2 == wallets[rep2]
        new_vc == [r \in Replicas |-> Max(wr1.vecclc[r],wr2.vecclc[r])]
        wr1_new ==[balance |-> wr1.balance,
                   v1cnt |-> MergePNCounters(wr1.v1cnt, wr2.v1cnt),
                   vecclc |-> new_vc]
    IN /\ \E r \in Replicas: wr1.v1cnt.p[r] < wr2.v1cnt.p[r]
       /\ wallets' = [wallets EXCEPT ! [rep1] = wr1_new]
       /\ Print("MergeBalance", TRUE)
       \*/\ Print(wallets', TRUE)
       
       
       
\* Amount of Money spent should be equal to the number of vouchers bought times the unit cost of the voucher in each replica  ---DOES NOT HOLD
ConservationOfMoney == \A r \in Replicas: EvalPNCounter(wallets[r].balance)  + EvalPNCounter(wallets[r].v1cnt)*V1Cost = 0

\* Balance in the wallet is always positive --- DOES NOT HOLD
PosBalance == \A rep \in Replicas: InitBal + EvalPNCounter(wallets[rep].balance) >= 0

FinalState(vc) == \A rep \in Replicas: vc[rep] = Natlim
EqualStates(st1, st2) == \A rep \in Replicas: st1.balance.p[rep] = st2.balance.p[rep] /\ st1.balance.n[rep] = st2.balance.n[rep] /\ st1.v1cnt.p[rep] = st2.v1cnt.p[rep] /\ st1.v1cnt.n[rep] = st2.v1cnt.n[rep]
\* Eventually all states converge to the same state ---DOES NOT HOLD
Convergence == \A r1 \in Replicas, r2 \in Replicas: FinalState(wallets[r1].vecclc) /\ FinalState(wallets[r2].vecclc) => EqualStates(wallets[r1], wallets[r2])

Next == \E r1 \in Replicas, r2 \in Replicas, qty \in 1..Qtylim: (BuyV1(r1,qty) \/ MergeCount(r1,r2) \/ MergeBalance(r1,r2)) 

Spec == Init /\ [] [Next]_<<wallets>>

THEOREM Spec => TypeInv /\ ConservationOfMoney /\ PosBalance /\ Convergence

=============================================================================
\* Modification History
\* Last modified Thu Sep 25 21:36:16 EEST 2014 by Suha
\* Created Thu Sep 25 21:01:10 EEST 2014 by Suha
