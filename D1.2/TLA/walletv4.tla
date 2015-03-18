------------------------------ MODULE walletv4 ------------------------------
EXTENDS Naturals, Sequences, TLC
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
    LET Sum[r \in SUBSET DOMAIN map] == 
		IF r ={} THEN 0 ELSE LET y == CHOOSE x \in r: TRUE 
						IN map[y]+ Sum[r\{y}]
    IN Sum[DOMAIN map]
    
EvalPNCounter(pnc) == SumAll(pnc.p) - SumAll(pnc.n) 

Max(n1,n2) == IF n1>= n2 THEN n1 ELSE n2

MergePNCounters(pnc1, pnc2) == 
	[p |-> [d \in DOMAIN pnc1.p |-> Max(pnc1.p[d], pnc2.p[d])], 
			n|-> [d \in DOMAIN pnc1.n |-> Max(pnc1.n[d], pnc2.n[d])] ]
    
-----------------------------------------------------------------------------

Wallet == [balance: PNCounter(Replicas),
           v1cnt: PNCounter(Replicas),
           vecclc: [Replicas ->Nat] ]
           

TypeInv == /\ wallets \in [Replicas->Seq(Wallet)]


Init == \*/\ Print ("a", TRUE)
        /\ wallets = [r \in Replicas |-> <<[balance |-> InitPNCounter(Replicas),
                                           v1cnt  |-> InitPNCounter(Replicas),
                                           vecclc |-> [r2 \in Replicas |-> 0] ]>>]
    
    
App(elt, s) == <<elt>> \o s

BuyV1(rep, qty) ==
    LET wr == Head(wallets[rep])
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
       /\ wallets' = [wallets EXCEPT ! [rep] = App(wr_new, wallets[rep]) ]
       /\ Print("Buy", TRUE)
      \* /\ Print(wallets', TRUE)

GetElt(seq, ind) == Head(SubSeq(seq,ind,ind))

Merge(rep1, rep2, ind) ==
    LET wr1 == Head(wallets[rep1])
        wr2 == GetElt(wallets[rep2], ind)
        new_vc == [r \in Replicas |-> Max(wr1.vecclc[r],wr2.vecclc[r])]
        wr1_new ==[balance |-> MergePNCounters(wr1.balance, wr2.balance),
                   v1cnt |-> MergePNCounters(wr1.v1cnt, wr2.v1cnt),
                   vecclc |-> new_vc]
    IN /\ \E r \in Replicas: wr1.vecclc[r] < wr2.vecclc[r]
       /\ wallets' = [wallets EXCEPT ! [rep1] = App(wr1_new, wallets[rep1]) ]
       /\ Print("Merge", TRUE)
       \*/\ Print(wallets', TRUE)
       
MergeLastStates(rep1, rep2) ==
    LET wr1 == Head(wallets[rep1])
        wr2 == Head(wallets[rep2])
        new_vc == [r \in Replicas |-> Max(wr1.vecclc[r],wr2.vecclc[r])]
        wr1_new ==[balance |-> MergePNCounters(wr1.balance, wr2.balance),
                   v1cnt |-> MergePNCounters(wr1.v1cnt, wr2.v1cnt),
                   vecclc |-> new_vc]
    IN /\ \E r \in Replicas: wr1.vecclc[r] < wr2.vecclc[r]
       /\ wallets' = [wallets EXCEPT ! [rep1] = App(wr1_new, wallets[rep1]) ]
       /\ Print("MergeLastStates", TRUE)
       \*/\ Print(wallets', TRUE)
       
       
\* Amount of Money spent should be equal to the number of vouchers bought times the unit cost of the voucher in each replica
ConservationOfMoney == \A r \in Replicas: EvalPNCounter(Head(wallets[r]).balance)  + 
	EvalPNCounter(Head(wallets[r]).v1cnt)*V1Cost = 0

\* Balance in the wallet is always positive --- DOES NOT HOLD
PosBalance == \A rep \in Replicas: InitBal + EvalPNCounter(Head(wallets[rep]).balance) >= 0

\* Fields of P and N fields of PN counters and vector clocks are monotonically nondecreasing in time
Monotonicity == /\ \A r \in Replicas, r2 \in Replicas, i \in Nat: (i>0 /\ i<Len(wallets[r]) ) => 
	(GetElt(wallets[r],i).vecclc[r2] >= GetElt(wallets[r],i+1).vecclc[r2]
    /\ GetElt(wallets[r],i).balance.p[r2] >= GetElt(wallets[r],i+1).balance.p[r2]
    /\ GetElt(wallets[r],i).balance.n[r2] >= GetElt(wallets[r],i+1).balance.n[r2]
	/\ GetElt(wallets[r],i).v1cnt.p[r2] >= GetElt(wallets[r],i+1).v1cnt.p[r2]
	/\ GetElt(wallets[r],i).v1cnt.n[r2] >= GetElt(wallets[r],i+1).v1cnt.n[r2])            

FinalState(vc) == \A rep \in Replicas: vc[rep] = Natlim
EqualStates(st1, st2) == \A rep \in Replicas: st1.balance.p[rep] = st2.balance.p[rep] /\ 
	st1.balance.n[rep] = st2.balance.n[rep] /\ 
	st1.v1cnt.p[rep] = st2.v1cnt.p[rep] /\ 
	st1.v1cnt.n[rep] = st2.v1cnt.n[rep]
\* Eventually all states converge to the same state
Convergence == \A r1 \in Replicas, r2 \in Replicas: 
	FinalState(Head(wallets[r1]).vecclc) /\ FinalState(Head(wallets[r2]).vecclc) => 
		EqualStates(Head(wallets[r1]), Head(wallets[r2]))

Next == \E r1 \in Replicas, r2 \in Replicas, qty \in 1..Qtylim(*, i \in Nat*): 
	(BuyV1(r1,qty) \/ (*Merge(r1,r2,i)*) MergeLastStates(r1,r2)) 

Spec == Init /\ [] [Next]_<<wallets>>

THEOREM Spec => TypeInv /\ ConservationOfMoney
=============================================================================
