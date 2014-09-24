------------------------- MODULE adCounterState_v0 -------------------------
EXTENDS Naturals, TLC

CONSTANTS 
    DC, \* Set of all data centers.
    DV, \* Set of all devices.
    AD, \* Set of all ads.
    maxTotalViews, \* Maximum number of times an ad should be shown.
    maxTotalViewsPerDC, \* Maximum number of times an ad should be shown in a data center. 
                        \* In this specification this partition is fixed.
    maxTotalViewsPerDevice, \* Maximum number of times an ad should be shown in a device.
    deviceAssignment \* Assignment of each device to a data center.
                     \* In this specification this assignment is fixed. 
          
Max(x, y) == IF x>y THEN x ELSE y
         
SumAll(func)==
    LET sum[v \in DOMAIN func] == 
        IF (DOMAIN func)\{v} = {} THEN func[v] ELSE func[v] + sum[(DOMAIN func)\{v}]
    IN sum[func]     
          
ASSUME maxTotalViews \in [AD -> Nat] 
ASSUME maxTotalViewsPerDevice \in [AD -> [DV -> Nat]] 
ASSUME deviceAssignment \in [DV -> DC]
ASSUME maxTotalViewsPerDC \in [DC -> [AD -> Nat]] 
    /\ \A a \in AD : SumAll([d \in DC |-> maxTotalViewsPerDC[d][a]]) = maxTotalViews[a]

VARIABLES configuration

------------------------------------------------------------------------------------------
\* Grow only counter
GCounter == [DC -> Nat]

\* Record that represents the local state of a data center.
\* Fields maxViews and devices are constant in the current specification,
\* but the plan is to add operations for moving devices and transfer view rights 
\* between data centers.
State ==
    [ads: SUBSET AD, \* Set of devices assigned to the shown on that data center
     devices: SUBSET DV, \* Set of devices assigned to the data center.
     (* maxViews: [ads-> Nat] *)
     maxViews: [AD -> Nat], \* Maximum number of times an ad should be shown in 
                            \* the data center. Used to transfer view rights.
     (* maxViews: [ads-> GCounter(DC)] *)
     views: [AD -> GCounter], \* G-Counter with overall views for each ad.
     (* viewsPerDevice: [ads-> [devices -> Nat]] *)
     viewsPerDevice: [AD -> [DV -> Nat]]] \* Number of views of each ad by a device.
                                          \* Because devices are assigned to a single data  
                                          \* center it is suficiente to keep the value of
                                          \* the local counter.

TypeInvariant == configuration \in [DC -> State]
    
Init == 
    /\ TypeInvariant
    /\ configuration = 
        [d \in DC |-> [ads |-> {a \in AD : maxTotalViewsPerDC[d][a] > 0},
                       devices |-> {g \in DV : deviceAssignment[g] = d},
                       maxViews |-> [a \in AD |-> maxTotalViewsPerDC[d][a]], 
                       views |-> [a \in AD |-> [d1 \in DC |-> 0]],
                       viewsPerDevice |-> [a \in AD |-> [g \in DV |-> 0]]]]
                       
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
        gc == state.views[a]
        new_state == 
            [ads |-> state.ads,
             devices |-> state.devices,
             maxViews |-> state.maxViews,
             views |-> [state.views EXCEPT ![a][d] = @+1],
             viewsPerDevice |-> [state.viewsPerDevice EXCEPT ![a][g] = @+1]]
    IN /\ a \in state.ads
       /\ g \in state.devices
       /\ gc[d] < state.maxViews[a]
       /\ state.viewsPerDevice[a][g] < maxTotalViewsPerDevice[a][g]
       /\ configuration' = [configuration EXCEPT ![d] = new_state]
       
Merge(d1, d2) == 
    LET state1 == configuration[d1]
        state2 == configuration[d2]
        new_state1 == 
            [ads |-> state1.ads,
             devices |-> state1.devices,
             maxViews |-> state1.maxViews,
             views |-> [a \in AD |->  [d \in DC |->
                    IF a \in state1.ads 
                    THEN Max(state1.views[a][d],state2.views[a][d])
                    ELSE 0]],
             viewsPerDevice |-> state1.viewsPerDevice]                        
  IN configuration' = [configuration EXCEPT ![d1] = new_state1] 

\* Operation for consulting the number of views of ad a.
Views(d,a) == SumAll(configuration[d].views[a])

------------------------------------------------------------------------------------------
      
Consistency == 
    \* The ad views do not exceed the total views limite.
    /\ \A d \in DC, a \in AD : Views(d,a) <= maxTotalViews[a]
    
    \* The views local to a data center do not exceed limite for that data center.
    /\ \A d \in DC, a \in AD : configuration[d].views[a][d] <= maxTotalViewsPerDC[a][d]
        
    \* The ad views by devices matches the total ad views.
    /\ \A d \in DC, a \in AD : SumAll(configuration[d].viewsPerDevice[a]) = Views(d,a)

    \* The ad views of a device do not exceed the views limite for that device.
    /\ \A d \in DC, a \in AD, g \in DV : 
            configuration[d].viewsPerDevice[a][g] <= maxTotalViewsPerDevice[a][g]
            
    \* A data center only keeps the views of devices assigned to it.   
    /\ \A d \in DC, a \in AD, g \in DV : 
        /\ g \notin configuration[d].devices => configuration[d].viewsPerDevice[a][g] = 0
        /\ a \notin configuration[d].ads => configuration[d].viewsPerDevice[a][g] = 0
    
    \* A data center only keeps the views of ads assigned to it.
    /\ \A d \in DC, a \in AD : a \notin configuration[d].ads => Views(d,a) = 0
    
    \* GCounter property:
    \* The local value of a gcounter has to be greater or equal to its value in other
    \* data centers.
    /\ \A d1 \in DC, d2 \in DC , a \in AD: 
            configuration[d1].views[a][d1] >= configuration[d2].views[a][d1]
  
Next == \E d1 \in DC, d2 \in DC, a \in AD, g \in DV : Inc(d1,a,g) \/ Merge(d1,d2) 
                
vars == <<configuration>> 
------------------------------------------------------------------------------------------            
Spec == Init /\ [][Next]_vars
------------------------------------------------------------------------------------------
THEOREM Spec => TypeInvariant /\ Consistency

==========================================================================================
\* Modification History
\* Last modified Thu Sep 18 11:06:20 WEST 2014 by carlaferreira
\* Created Wed Sep 10 22:06:30 CEST 2014 by carlaferreira
