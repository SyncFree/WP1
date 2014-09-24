-------------------------------- MODULE adCounterState_v0 --------------------------------
EXTENDS Naturals

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

VARIABLES configuration

------------------------------------------------------------------------------------------

GCounter == [DC -> Nat]

\* Record that represents the local state of a data center.
\* Fields maxViews and devices are constant in the current specification,
\* but the plan is to add operations for moving devices and transfer view rights 
\* between data centers.
State ==
    [maxViews: [AD -> Nat], \* Maximum number of times an ad should be shown in 
                            \* the data center.
    devices: SUBSET DV, \* Set of devices assigned to the data center.
    views: [AD -> GCounter], \* G-Counter with overall views for each ad.
    viewsPerDevice: [AD -> [DV -> Nat]]] \* Number of views of each ad by a device.
                                         \* Note: Because devices are assigned to a single  
                                         \* data center it is suficiente to keep the value 
                                         \* of the local counter.
 
TypeInvariant == configuration \in [DC -> State]

Init == 
    /\ TypeInvariant
    /\ configuration = 
        [d \in DC |-> [maxViews |-> [a \in AD |-> maxTotalViewsPerDC[d][a]], 
                       devices |-> {g \in DV : deviceAssignment[g] = d}, 
                       views |-> [a \in AD |-> [dc1 \in DC |-> 0]],
                       viewsPerDevice |-> [a \in AD |-> [g \in DV |-> 0]]]] 
                       /Users/carlaferreira/GitHub/WP1/D1.2/TLA/adCounterState_v0.tla
------------------------------------------------------------------------------------------     
    
\* Local operation at data center d that represents a visualisation of 
\* the advert a in device g at time t. 
\* Pre:  - Device g is assigned to data center d.
\*       - The data center view limit for ad a is not exceeded.
\*       - The device view limit for ad a in device g is not exceeded.
\* Post: - The data center local state is updated, in particular, 
\*       - the views G-Counter and viewsPerDevice is incremented by one.   
Inc(d, a, g) == 
    LET state == configuration[d]
        new_state == 
            [maxViews |-> state.maxViews,
             devices |-> state.devices,
             views |-> [state.views EXCEPT ![a][d] = @+1],
             viewsPerDevice |-> [state.viewsPerDevice EXCEPT ![a][g] = @+1]]
    IN /\ g \in state.devices
       /\ state.views[a][d] < state.maxViews[a]
       /\ state.viewsPerDevice[a][g] < maxTotalViewsPerDevice[a][g]
       /\ configuration' = [configuration EXCEPT ![d] = new_state]

Max(x,y) == IF x>y THEN x ELSE y 

\* Operation for merging the state of d1 with state of d2.
\* Pre:  - true
\* Post: - Merges the fields views and viewsPerDevice, by pairwise picking the
\*         maximum value of data centers d1 and d2.
Merge(d1, d2) == 
    LET state1 == configuration[d1]
        state2 == configuration[d2]
        new_state1 == 
            [maxViews |-> state1.maxViews,
             devices |-> state1.devices,
             views |-> [a \in AD |-> [d \in DC |-> 
                        Max(state1.views[a][d],state2.views[a][d])]],
             viewsPerDevice |-> [a \in AD |-> [g \in DV |-> 
                            Max(state1.viewsPerDevice[a][g],state2.viewsPerDevice[a][g])]]]
  IN configuration' = [configuration EXCEPT ![d1] = new_state1] 
  

\* Operation for consulting the number of views of ad a.
Value(d,a) == sumAll(configuration[d].views[a])

------------------------------------------------------------------------------------------
      
Consistency == 
    \* The ad views do not exceed the total views limite.
    /\ \A d \in DC, a \in AD : Value(d,a) <= maxTotalViews[a]
    
    \* The views local to a data center do not exceed limite for that data center.
    /\ \A d \in DC, a \in AD : configuration[d].views[a][d] <= maxTotalViewsPerDC[a][d]

    \* The ad views of a device do not exceed the views limite for that device.
    /\ \A d \in DC, a \in AD, g \in DV : 
            configuration[d].viewsPerDevice[a][g] <= maxTotalViewsPerDevice[a][g]
    
    \* The ad views by devices matches the total ad views.
    /\ \A d \in DC, a \in AD : sumAll(configuration[d].viewsPerDevice[a]) = Value(d,a)
    
  
Next == \E d1 \in DC, d2 \in DC, a \in AD, g \in DV : Inc(d1,a,g) \/ Merge(d1,d2) 
                
vars == <<configuration>> 
------------------------------------------------------------------------------------------            
Spec == Init /\ [][Next]_vars
------------------------------------------------------------------------------------------
THEOREM Spec => TypeInvariant /\ Consistency

==========================================================================================
\* Modification History
\* Last modified Thu Sep 04 17:35:05 WEST 2014 by carlaferreira
\* Created Tue Sep 02 07:36:31 WEST 2014 by carlaferreira
