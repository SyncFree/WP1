-------------------------------- MODULE adCounterState_v2 --------------------------------

EXTENDS Naturals, GCounters

CONSTANTS 
    DV, \* Set of all devices.
    DC, \* Set of all data centers.
    maxTotalViews, \* Maximum number of times the ad should be shown.
    maxTotalViewsPerDC, \* Maximum number of times the ad should be shown in a data center. 
                        \* In this specification this partition is fixed.
    maxTotalViewsPerDevice, \* Maximum number of times the ad should be shown in a device.
    deviceAssignment \* Assignment of each device to a data center.
                     \* In this specification this assignment is fixed.           
SumAll(map) ==
    LET Sum[r \in SUBSET DOMAIN map] == IF r ={} THEN 0 ELSE 
        LET y == CHOOSE x \in r: TRUE IN map[y]+ Sum[r\{y}]
    IN Sum[DOMAIN map]
          
ASSUME maxTotalViews \in Nat
ASSUME maxTotalViewsPerDevice \in [DV -> Nat]
ASSUME deviceAssignment \in [DV -> DC]
ASSUME maxTotalViewsPerDC \in [DC -> Nat] 
 /\ SumAll([d \in DC |-> maxTotalViewsPerDC[d]]) = maxTotalViews

VARIABLES configuration

------------------------------------------------------------------------------------------

\* Record that represents the local state of a data center.
\* Fields maxViews and devices are constant in the current specification,
\* but the plan is to add operations for moving devices and transfer view rights 
\* between data centers.
State ==
    [   devices: SUBSET DV, \* Set of devices assigned to the data center.
        maxViews: Nat, \* Maximum number of times the ad should be shown in 
                       \* the data center. Used to transfer view rights.
        views: GCounter(DC), \* G-Counter with overall views for the ad.
 
        viewsPerDevice: [DV -> Nat]] \* Number of views by a device.
                                     \* Note: Because devices are assigned to a single  
                                     \* data center it is suficiente to keep the value 
                                     \* of the local counter.

TypeInvariant == configuration \in [DC -> State]
    
Init == 
    /\ TypeInvariant
    /\ configuration = 
        [d \in DC |-> [devices |-> {g \in DV : deviceAssignment[g] = d}, 
                       maxViews |-> maxTotalViewsPerDC[d], 
                       views |-> GCounterInit(DC),
                       viewsPerDevice |-> [g \in DV |-> 0]]]
                       
------------------------------------------------------------------------------------------    
    
\* Local operation at data center d that represents a visualisation of 
\* the advert in device g at time t. 
\* Pre:  - Device g is assigned to data center d.
\*       - The data center view limit for the ad is not exceeded.
\*       - The device view limit for ad a in device g is not exceeded.
\* Post: - The data center local state is updated, in particular, 
\*       - the views G-Counter and viewsPerDevice is incremented by one.   
Inc(d, g) == 
    LET state == configuration[d]
        gc == state.views
        new_state == 
            [devices |-> state.devices,
             maxViews |-> state.maxViews,
             views |-> GCounterInc(gc,d),
             viewsPerDevice |-> [state.viewsPerDevice EXCEPT ![g] = @+1]]
    IN /\ g \in state.devices
       /\ GCounterValueAt(gc,d) < state.maxViews
       /\ state.viewsPerDevice[g] < maxTotalViewsPerDevice[g]
       /\ configuration' = [configuration EXCEPT ![d] = new_state]
       
Merge(d1, d2) == 
    LET state1 == configuration[d1]
        state2 == configuration[d2]
        new_state1 == 
            [devices |-> state1.devices,
             maxViews |-> state1.maxViews,
             views |-> GCounterMerge(state1.views,state2.views),
             viewsPerDevice |-> state1.viewsPerDevice]           
  IN configuration' = [configuration EXCEPT ![d1] = new_state1] 

\* Operation for consulting the number of views of ad a.
Views(d) == SumAll(configuration[d].views)

------------------------------------------------------------------------------------------
      
Consistency == 
    \* The ad views do not exceed the total views limite.
    /\ \A d \in DC: Views(d) <= maxTotalViews
    
    \* The views local to a data center do not exceed limite for that data center.
    /\ \A d \in DC : configuration[d].views[d] <= maxTotalViewsPerDC[d]

    \* The ad views of a device do not exceed the views limite for that device.
    /\ \A d \in DC, g \in DV : 
            configuration[d].viewsPerDevice[g] <= maxTotalViewsPerDevice[g]
            
    \* A data center only keeps the views of devices assigned to it.
    \* Needed because it is not possible to define partial functions in TLA.     
    /\ \A d \in DC, g \in DV : 
        /\ g \notin configuration[d].devices => configuration[d].viewsPerDevice[g] = 0
  
    \* The ad views by devices matches the total ad views.
    /\ \A d \in DC : SumAll(configuration[d].viewsPerDevice) = Views(d)
    
    \* GCounter property:
    \* The local value of a gcounter has to be greater or equal to the value in other.
    /\ \A d1 \in DC, d2 \in DC :
            configuration[d1].views[d1] >= configuration[d2].views[d1]
  
Next == \E d1 \in DC, d2 \in DC, g \in DV : Inc(d1,g) \/ Merge(d1,d2) 
                
vars == <<configuration>> 
------------------------------------------------------------------------------------------            
Spec == Init /\ [][Next]_vars
------------------------------------------------------------------------------------------
THEOREM Spec => TypeInvariant /\ Consistency

==========================================================================================
\* Modification History
\* Last modified Tue Oct 21 12:32:25 WEST 2014 by carlaferreira
\* Created Wed Sep 10 22:06:30 CEST 2014 by carlaferreira
