--------------------------- MODULE leaderBoard_v2 ---------------------------
EXTENDS Naturals, TLC, FiniteSets
VARIABLES scores, vecclc
CONSTANTS DC, Games, Players, PlayersByGame

ASSUME PlayersByGame \in [Games -> SUBSET Players]
-----------------------------------------------------------------------------
\* Function for converting Game-Player information function to tuple form
MapProduct(map) ==
    LET mp[s \in SUBSET DOMAIN map] == 
		IF s={} THEN {} 
				ELSE LET y == CHOOSE x \in s: TRUE 
					 IN ({y} \X map[y]) \cup mp[s\{y}]
    IN mp[DOMAIN map]

GamePlayers == MapProduct(PlayersByGame)

\* scores is a function from Data Centers to the games to the players playing this game to the Nat
\* vecclc is a ghost variable keeping vector clock for each player in each game for each data centerr
TypeInv == /\ scores \in [DC ->[MapProduct(PlayersByGame) -> Nat]]
           /\ vecclc \in [GamePlayers -> [DC -> [DC -> Nat]]]

\* Operator that returns the set that contains the players who lead in the game g according to data center d
Leaders(d,g) == {x \in PlayersByGame[g] : \A y \in PlayersByGame[g]: scores[d][<<g,x>>] >= scores[d][<<g,y>>]}
   
\* Operator for finding set of players who ranks ith in game g according to the data center d 
Rank(d,g,i) == 
    LET RankSets[j \in 1..i] == IF j=1 THEN Leaders(d,g) 
                                ELSE LET remaining ==  PlayersByGame[g] \ RankSets[j-1] 
                                     IN RankSets[j-1] \cup 
								 {x \in remaining : \A y \in remaining: 
								scores[d][<<g,x>>] >= scores[d][<<g,y>>]}             
    IN  IF i =1 THEN Leaders(d,g) ELSE RankSets[i] \ RankSets[i-1]



\* Initialize each field of every variable to zero
Init == /\ scores = [d \in DC |-> [ a \in GamePlayers |-> 0]]
        /\ vecclc = [g \in GamePlayers |-> [d \in DC |-> [dc \in DC |-> 0]]]

\* An operation that updates the score of a user in a particular game and data center
(* PRE: - p must be a player of game g
        - new score entered must be greater than the current score of the user
        - number of updates for this player must be within natural numbers limit
   POST: - update field of the scores variable corresponding to the player p for game g in data center d
        - increment d field of the vector clock of the player p in game g for the data center d by 1 *)
UpdateScore(dc,g,p,scr) == /\ <<g,p>> \in GamePlayers
                           /\ scr > scores[dc][<<g,p>>]
                           /\ scores' = [scores EXCEPT ! [dc][<<g,p>>] = scr]
                           /\ vecclc[<<g,p>>][dc][dc]+1 \in Nat
                           /\ vecclc' = [vecclc EXCEPT ! [<<g,p>>][dc][dc] = vecclc[<<g,p>>][dc][dc]+1]

\* A helper function for finding maximum of two numerals 
Max(n1,n2) == IF n1 >= n2 THEN n1 ELSE n2

\* An operation that merges the score of player p in game g in data center d1 with the same field in data center d2
(* PRE: - p must be a player of game g
        - score of p in data center d2 for game g must be greater than the corresponding score in data center d2
   POST:- update the field of the scores' variable corresponding to player p for game g in data center d1 by merging
        the scores kept in d1 and d2
        - merge the vector clock of player p for game g in data center d with the vector clock of the same user for the same game
        in data center d2 *)
Merge(d1,d2,g,p) == /\ <<g,p>> \in GamePlayers
                    /\ scores[d2][<<g,p>>] > scores[d1][<<g,p>>]
                    /\ scores' = [scores EXCEPT ! [d1][<<g,p>>] = scores[d2][<<g,p>>] ]
                    /\ LET new_vc == [d \in DC |-> 
						Max(vecclc[<<g,p>>][d1][d],vecclc[<<g,p>>][d2][d]) ] 
		IN  vecclc' = [vecclc EXCEPT ! [<<g,p>>][d1] = new_vc]
                    /\ LET a== <<"MERGE",d1,g,2,Rank(d1,g,2),scores>> IN Print(a,TRUE)


              
Next == \E d \in DC, d2 \in DC, g \in Games, p \in Players, scr \in Nat: (UpdateScore(d,g,p,scr) \/ Merge(d,d2,g,p))

Spec == Init /\ [][Next]_<<scores,vecclc>>

\* Eventual Consistency invariant stating that scores variable eventually converges 
Convergence == <> \A d1 \in DC, d2 \in DC, g \in Games, p \in Players: 
	<<g,p>> \in GamePlayers => scores[d1][<<g,p>>] = scores[d2][<<g,p>>] 
\* if the vector clock for the all players playing game g in data center d1 is <= vector clocks of the same players for game g in data center 
\* d2 then Leader's score for g in d1 must be >= Leader's score for g in d2
MonotonicLeader == \A d1 \in DC, d2 \in DC, g \in Games: 
    (\A p \in Players: <<g,p>> \in GamePlayers => 
		(\A d \in DC: vecclc[<<g,p>>][d1][d] <= vecclc[<<g,p>>][d2][d])) => 
			scores[d1][<<g, CHOOSE x \in Leaders(d1,g):TRUE >>] <= 
			scores[d2][<<g, CHOOSE x \in Leaders(d2,g):TRUE>>]

=============================================================================
