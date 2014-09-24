--------------------------- MODULE adCounterOp_v0 ---------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS 
    DV, \* Set of all devices.
    DC, \* Set of all data centers.
    AD, \* Set of all ads.
    maxTotalViews, \* Maximum number of times an ad should be shown.
    maxTotalViewsPerDC, \* Maximum number of times an ad should be shown in a data center. 
                        \* In this specification this partition is fixed.
    maxTotalViewsPerDevice, \* Maximum number of times an ad should be shown in a device.
    deviceAssignment \* Assignment of each device to a data center.
                     \* In this specification this assignment is fixed. 
          
RECURSIVE sumAll(_)
\* Auxiliary operation that given a function f:X -> Nat
\* returns the summation of all numbers in the range of f.
sumAll(f) == 
    IF DOMAIN f = {} THEN 0
    ELSE LET v == CHOOSE x \in DOMAIN f : TRUE 
         IN f[v] + sumAll([a \in DOMAIN f \ {v} |-> f[a]])
          
ASSUME maxTotalViews \in [AD -> Nat] 
ASSUME maxTotalViewsPerDevice \in [AD -> [DV -> Nat]] 
ASSUME deviceAssignment \in [DV -> DC]
\* maxTotalViewsPerDC defines a partition of views between data centers.
ASSUME maxTotalViewsPerDC \in [DC -> [AD -> Nat]] /\ \A a \in AD : 
        (sumAll([d \in DC |-> maxTotalViewsPerDC[d][a]]) = maxTotalViews[a])

VARIABLES configuration, msgs

------------------------------------------------------------------------------------------
VectorClock == [DC -> Nat]

\* Record that represents the local state of a data center.
\* Fields maxViews and devices are constant in the current specification,
\* but the plan is to add operations for moving devices and transfer view rights 
\* between data centers.
State ==
    [maxViews: [AD -> Nat], \* Maximum number of times an ad should be shown in 
                            \* the data center.
    devices: SUBSET DV, \* Set of devices assigned to the data center.
    views: [AD -> Nat], \* Total views for each ad.
    viewsPerDevice: [AD -> [DV -> Nat]], \* Number of views of each ad by a device.
    vClock: [AD -> VectorClock]] \* Vector clock
    
\* remote operations to be propagated as messages.
RemoteOp == 
    [dc: DC, \* Data center where operation executed locally.
     ad: AD,  \* Advert.
     device: DV, \* Device. 
     vClock: [DC -> Nat]] \* vector clock at local replica for the ad.
 
 
TypeInvariant == 
    /\ configuration \in [DC -> State] 
    /\ msgs \in [DC -> SUBSET RemoteOp] 

Init == 
    /\ TypeInvariant
    /\ configuration = 
        [d \in DC |-> [maxViews |-> [a \in AD |-> maxTotalViewsPerDC[d][a]], 
                       devices |-> {g \in DV : deviceAssignment[g] = d}, 
                       views |-> [a \in AD |-> 0],
                       viewsPerDevice |-> [a \in AD |-> [g \in DV |-> 0]],
                       vClock |-> [a \in AD |-> [dc \in DC |-> 0]]]]    
    /\ msgs = [d \in DC |-> {}]
    
------------------------------------------------------------------------------------------    
    
\* Local operation at data center d that represents a visualisation of 
\* the advert a in device g at time t. 
\* Pre:  - Device g is assigned to data center d.
\*       - The data center view limit for ad a is not exceeded.
\*       - The device view limit for ad a in device g is not exceeded.
\*       - Vector clock is updated.
\*       - Operation is propagated to all other replicas.   
Inc(d, a, g) == 
    LET state == configuration[d]
        new_vClock == [state.vClock EXCEPT ![a][d] = @+1]
        new_state == 
            [maxViews |-> state.maxViews,
             devices |-> state.devices,
             views |-> [state.views EXCEPT ![a] = @+1],
             viewsPerDevice |-> [state.viewsPerDevice EXCEPT ![a][g] = @+1],
             vectorClock |-> new_vClock]
        downstream == [dc |-> d, ad |-> a, device |-> g, vClock |-> new_vClock[a]]
    IN /\ g \in state.devices
       /\ state.views[a] < state.maxViews[a]
       /\ state.viewsPerDevice[a][g] < maxTotalViewsPerDevice[a][g]
       /\ configuration' = [configuration EXCEPT ![d] = new_state]
       /\ msgs' = [dc \in DC |-> IF dc = d THEN msgs[d] ELSE msgs[dc] \cup {downstream}]

Max(x,y) == IF x>y THEN x ELSE y 

LessThanVC(vc1,vc2) == /\ \A d \in DC : vc1[d] <= vc2[d] 
                   /\ \E d \in DC : vc1[d] <  vc2[d]

\* Operation that represents a remote execution of an operation.
\* Pre: - Selects a remote operation op waiting to be executed, 
\*        that satisfies causal consistency.
\*      - Remote operation preconditions where already verified locally, 
\*        so they should not be verified again.
\* Post: - views are updtated; 
\*       - Remote operation is removed from msgs 
RemoteInc(d) == 
  \E op \in msgs[d] :
  LET state == configuration[d]
      new_vClock == 
            [state.vClock EXCEPT ![op.ad] = [dc \in DC |-> IF dc = op.dc
                THEN state.vClock[op.ad][op.dc]+1 
                ELSE Max(state.vClock[op.ad][dc],op.vClock[op.ad][op.dc])]]
      new_state == 
            [maxViews |-> state.maxViews,
             devices |-> state.devices,
             views |-> [state.views EXCEPT ![op.ad] = @+1],
             viewsPerDevice |-> [state.viewsPerDevice EXCEPT ![op.ad][op.device] = @+1],
             vectorClock |-> new_vClock]
  IN /\ \A op1 \in msgs[d] : 
                op1.ad = op.ad => \neg LessThanVC(op1.vClock[op.ad],op.vClock[op.ad])
     /\ configuration' = [configuration EXCEPT ![d] = new_state]
     /\ msgs' = [msgs EXCEPT ![d] =  msgs[d] \ {op} ] 

\* Operation for consulting the number of views of ad a.
Value(d,a) == configuration[d].views[a]

------------------------------------------------------------------------------------------
       
Consistency == 
    \* The ad views plus the remote operations not yet executed do not exceed 
    \* the total views limite.
    /\ \A d \in DC, a \in AD : 
        Value(d,a) + Cardinality({op \in msgs[d]: op.ad = a}) <= maxTotalViews[a]
        
    \* The ad views of a device plus the remote operations not yet executed do not exceed 
    \* the views limite for that device.
    /\ \A d \in DC, a \in AD, g \in DV : 
        configuration[d].viewsPerDevice[a][g] 
                + Cardinality({op \in msgs[d]: op.ad = a /\ op.device = g})
        <= maxTotalViewsPerDevice[a][g]
    
    \* The ad views by devices matches the total ad views.
    /\ \A d \in DC, a \in AD : sumAll(configuration[d].viewsPerDevice[a]) = Value(d,a)
    
    \* If all remote operations have been propagated, then data centers have converged. 
    /\ \A d1 \in DC, d2 \in DC :  
            msgs[d1] = {} /\ msgs[d2] = {} => 
                \A a \in AD : configuration[d1].views[a] = configuration[d1].views[a]
  
Next == \E d \in DC, a \in AD, g \in DV : Inc(d,a,g) \/ RemoteInc(d) 
                
vars == <<configuration,msgs>> 
------------------------------------------------------------------------------------------            
Spec == Init /\ [][Next]_vars
------------------------------------------------------------------------------------------
THEOREM Spec => TypeInvariant /\ Consistency

==========================================================================================
\* Modification History
\* Last modified Fri Sep 05 09:38:33 WEST 2014 by carlaferreira
\* Created Wed Sep 03 21:40:34 WEST 2014 by carlaferreira
