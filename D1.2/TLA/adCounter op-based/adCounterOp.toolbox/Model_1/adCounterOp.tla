---------------------------- MODULE adCounterOp ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS 
    DV, \* Set of all devices.
    DC, \* Set of all data centers.
    maxTotalViews, \* Maximum number of times an ad should be shown.
    maxTotalViewsPerDC, \* Maximum number of times an ad should be shown in a data center. 
                        \* In this specification this partition is fixed.
    maxTotalViewsPerDevice, \* Maximum number of times an ad should be shown in a device.
    deviceAssignment \* Assignment of each device to a data center.
                     \* In this specification this assignment is fixed. 
          
sumAll(map) ==
    LET Sum[r \in SUBSET DOMAIN map] == IF r ={} THEN 0 ELSE 
        LET y == CHOOSE x \in r: TRUE IN map[y]+ Sum[r\{y}]
    IN Sum[DOMAIN map]
    
          
ASSUME maxTotalViews \in Nat 
ASSUME maxTotalViewsPerDevice \in [DV -> Nat] /\ 
 \A g \in DV : maxTotalViewsPerDevice[g] > 0
ASSUME deviceAssignment \in [DV -> DC]
\* maxTotalViewsPerDC defines a partition of views between data centers.
ASSUME maxTotalViewsPerDC \in [DC -> Nat] /\ 
  (sumAll([d \in DC |-> maxTotalViewsPerDC[d]]) = maxTotalViews)

VARIABLES configuration, msgs

------------------------------------------------------------------------------------------
VectorClock == [DC -> Nat]

\* Record that represents the local state of a data center.
\* Fields maxViews and devices are constant in the current specification,
\* but the plan is to add operations for moving devices and transfer view rights 
\* between data centers.
State ==
    [maxViews: Nat, \* Maximum number of times an ad should be shown in 
                            \* the data center.
    devices: SUBSET DV, \* Set of devices assigned to the data center.
    views: Nat, \* Total views for each ad.
    viewsPerDevice: [DV -> Nat], \* Number of views of each ad by a device.
    vclock: VectorClock] \* Vector clock
    
\* remote operations to be propagated as messages.
RemoteOp == 
    [dc: DC, \* Data center where operation executed locally.
     device: DV, \* Device. 
     vclock: VectorClock] \* vector clock at local replica for the ad.
 
 
TypeInvariant == 
    /\ configuration \in [DC -> State] 
    /\ msgs \in [DC -> SUBSET RemoteOp] 

Init == 
    /\ TypeInvariant
    /\ configuration = [d \in DC |-> [maxViews |-> maxTotalViewsPerDC[d], 
                                    devices |-> {g \in DV : deviceAssignment[g] = d}, 
                                    views |-> 0,
                                    viewsPerDevice |-> [g \in DV |-> 0],
                                    vclock |-> [dc \in DC |-> 0]]]    
    /\ msgs = [d \in DC |-> {}]
    
------------------------------------------------------------------------------------------    
    
\* Local operation at data center d that represents a visualisation of 
\* the advert a in device g at time t. 
\* Pre:  - Device g is assigned to data center d.
\*       - The data center view limit is not exceeded.
\*       - The device view limit for device g is not exceeded.
\*       - Vector clock is updated.
\*       - Operation is propagated to all other replicas.   
Inc(d, g) == 
    LET state == configuration[d]
        new_vclock == [state.vClock EXCEPT ![d] = @+1]
        new_state == 
            [maxViews |-> state.maxViews,
             devices |-> state.devices,
             views |-> state.views + 1,
             viewsPerDevice |-> [state.viewsPerDevice EXCEPT ![g] = @+1],
             vclock |-> new_vclock]
        downstream == [dc |-> d, device |-> g, vclock |-> new_vclock]
    IN /\ g \in state.devices
       /\ state.views < state.maxViews
       /\ state.viewsPerDevice[g] < maxTotalViewsPerDevice[g]
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
      new_vclock == [dc \in DC |-> IF dc = d
                THEN state.vClock[d]+1 
                ELSE Max(state.vclock[dc],op.vclock[op.dc])]
      new_state == 
            [maxViews |-> state.maxViews,
             devices |-> state.devices,
             views |-> state.views + 1,
             viewsPerDevice |-> [state.viewsPerDevice EXCEPT ![op.device] = @+1],
             vectorclock |-> new_vclock]
  IN /\ \A op1 \in msgs[d] : \neg LessThanVC(op1.vclock,op.vclock)
     /\ configuration' = [configuration EXCEPT ![d] = new_state]
     /\ msgs' = [msgs EXCEPT ![d] =  msgs[d] \ {op} ] 

\* Operation for consulting the number of views of ad a.
Value(d) == configuration[d]

------------------------------------------------------------------------------------------
       
Consistency == 
    \* The ad views plus the remote operations not yet executed do not exceed 
    \* the total views limite.
    /\ \A d \in DC : 
        Value(d) + Cardinality(msgs[d]) <= maxTotalViews
        
    \* The ad views of a device plus the remote operations not yet executed do not exceed 
    \* the views limite for that device.
    /\ \A d \in DC, g \in DV : 
        configuration[d].viewsPerDevice[g] 
                + Cardinality({op \in msgs[d]: op.device = g})
        <= maxTotalViewsPerDevice[g]
    
    \* The ad views by devices matches the total ad views.
    /\ \A d \in DC : sumAll(configuration[d].viewsPerDevice) = Value(d)
    
    \* If all remote operations have been propagated, then data centers have converged. 
    \* same massages pending
    /\ \A d1 \in DC, d2 \in DC :  
            msgs[d1] = {} /\ msgs[d2] = {} => 
                configuration[d1].views = configuration[d1].views 
  
Next == \E d \in DC, g \in DV : Inc(d,g) \/ RemoteInc(d) 
                
vars == <<configuration,msgs>> 
------------------------------------------------------------------------------------------            
Spec == Init /\ [][Next]_vars
------------------------------------------------------------------------------------------
THEOREM Spec => TypeInvariant /\ Consistency

=============================================================================
\* Modification History
\* Last modified Tue Oct 21 15:03:10 WEST 2014 by carlaferreira
\* Created Mon Oct 20 16:18:11 WEST 2014 by carlaferreira
