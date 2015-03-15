----------------------------- MODULE walletNat -----------------------------
EXTENDS Integers, TLC, Naturals
VARIABLE wallets
CONSTANTS Replicas, V1Cost, InitBal, Natlim, Qtylim

(*ASSUME /\ V1Cost \in Nat
       /\ InitBal \in Int
       /\ Natlim \in Nat
       /\ Qtylim \in Nat
       /\ V1Cost > 0
       /\ InitBal > 0
       /\ Natlim > 0
       /\ Qtylim > 0*)

----------------------------------------------------------------------------

Wallet == [balance: Int,
           v1cnt: Int,
           vecclc: [Replicas->Nat]]

TypeInv == /\ wallets \in [Replicas -> Wallet]

Init ==  /\ wallets = [r \in Replicas |-> [balance |-> InitBal,
                                           v1cnt |-> 0,
                                           vecclc |-> [r2 \in Replicas |-> 0] ] ]
        /\Print(wallets, TRUE)
                                           
BuyV1(rep, qty) == 
    LET wr == wallets[rep]
        new_vc == [wr.vecclc EXCEPT ! [rep] = wr.vecclc[rep] + 1]
        new_wr == [balance |-> wr.balance - qty*V1Cost,
                   v1cnt |-> wr.v1cnt + qty,
                   vecclc |-> new_vc]
    IN /\ wr.balance >= qty*V1Cost
       /\ wr.v1cnt + qty <= Natlim
       /\ wr.vecclc[rep]+1 <= Natlim
       /\ wallets' = [wallets EXCEPT ! [rep] = new_wr]
      \* /\ Print("Buy", TRUE)
       \*/\ Print(wallets', TRUE)
       
Max(n1,n2) == IF n1>= n2 THEN n1 ELSE n2

Merge(r1,r2) == 
    LET wr1 == wallets[r1]
        wr2 == wallets[r2]
        new_vc == [r \in Replicas |-> Max(wr1.vecclc[r], wr2.vecclc[r])]
        new_w1 == [balance |-> Max(wr1.balance, wr2.balance),
                   v1cnt |-> Max(wr1.v1cnt, wr2.v1cnt), \* wr1.v1cnt+wr2.v1cnt, \*alternative formulation
                   vecclc |-> new_vc]
                   
    IN /\ \E r \in Replicas: wr1.vecclc[r] < wr2.vecclc[r]
       /\ wallets' = [wallets EXCEPT ! [r1] = new_w1]
       \*/\ Print("Merge", TRUE)
       \*/\ Print(wallets', TRUE)
       
       
ConservationOfMoney == \A r \in Replicas: (InitBal - wallets[r].balance) >= wallets[r].v1cnt*V1Cost

FinalState(vc) == \A r \in Replicas: vc[r] = Natlim
EqualStates(st1,st2) == st1.balance = st2.balance /\ st1.v1cnt = st2.v1cnt
Convergence == \A r1 \in Replicas, r2 \in Replicas: FinalState(wallets[r1].vecclc) /\ FinalState(wallets[r2].vecclc) => EqualStates(wallets[r1],wallets[r2])

Next == \E r1 \in Replicas, r2 \in Replicas, qty \in 1..Qtylim: (BuyV1(r1,qty) \/ Merge(r1,r2))

Spec == Init /\ [] [Next]_<<wallets>>

THEOREM Spec => TypeInv /\ ConservationOfMoney /\ Convergence 
=============================================================================
