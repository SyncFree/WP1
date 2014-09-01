-------------------------- MODULE adCounter_v2 --------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Ads, \* Set of all adverts (non-empty).
          Devices, \* Set of all devices (non-empty).
          Replicas \* Set of all replicas (non-empty).
          
ASSUME IsFiniteSet(Ads) /\ Ads /= {} 
ASSUME IsFiniteSet(Devices) /\ Devices /= {}
ASSUME IsFiniteSet(Replicas) /\ Replicas /= {}

          
VARIABLES 
        \* viewsPerAd_GC[r][a] is the local state of replica r that stores
        \* the number of views of advert a.
    viewsPerAd,
    
        \* viewsPerDevice_[r][a][d] is the local state of replica r that 
        \* stores the number of views for advert a in device d.    
    viewsPerDevice,
        
        \* viewsPerDeviceTime[r][a][d] is the local state of replica r that  
        \* stores the sequence of time-stamps advert a was shown in device d.
    viewsPerDeviceTime,
       
        \* numLocalOps[r] is the number of operations executed locally in 
        \* replica r.
    numLocalOps,
    
        \* numRemoteOps[r] is the number of remote operations executed in 
        \* replica r.
    numRemoteOps,
    
        \* msgs[r] set of remote operations waiting to be executed at 
        \* replica r.
    msgs,
        
        \* schedule[a].start and schedule[a].end define, respectivelly, the 
        \* start and ending time for advert a.
    schedule,
    
        \* boundsTotal[a] defines the maximum number of times advert a should 
        \* be shown.
    boundsTotal,
        
        \* boundsPerDevice[a][d] defines the maximum number of times advert a 
        \* should be shown in device d.
    boundsPerDevice,
    
        \* stockPerDC[r] defines the maximum number of times advert a should 
        \* be shown in a replica (or data center).
    stockPerReplica,
        
        \* deviceReplica[d] defines the replica device d is assigned to
        \* for all adverts. 
    replicaOfDevice

--------------------------------------------------------------

RemoteOp == \* remote operations to be propagated as messages
    [replica: Replicas, \* replica where operation executed locally.
     adId: Ads, \* advert id. 
     deviceId: Devices, \* advert id. 
     time: Nat, \* time of execution at remote replica.
     order: Nat ] \* operation order of execution within local replica.
     
RECURSIVE sumAll(_)
\* Auxiliary operation that given a function f:X->Nat
\* returns the summation of all numbers in the range of f.
sumAll(f) == 
    IF f = {} THEN 0
    ELSE LET v == CHOOSE x \in DOMAIN f : TRUE 
         IN f[v] + sumAll([a \in DOMAIN f \ {v} |-> f[a]])

TypeInvariant == 
    /\ viewsPerAd \in [Replicas -> [Ads -> Nat]]
    /\ viewsPerDevice \in [Replicas -> [Ads -> [Devices ->Nat]]]
    /\ viewsPerDeviceTime \in [Replicas -> [Ads -> [Devices -> Seq(Nat)]]]
    /\ numLocalOps \in [Replicas -> Nat]
    /\ numRemoteOps \in [Replicas -> Nat]
    /\ msgs \in [Replicas -> SUBSET RemoteOp] 
    /\ schedule \in [Ads -> [start: Nat, end:Nat]]
    /\ boundsTotal \in [Ads -> Nat]
    /\ boundsPerDevice \in [Ads -> [Devices -> Nat]] 
    /\ stockPerReplica \in [Replicas -> [Ads -> Nat]]
    /\ replicaOfDevice \in [Devices -> Replicas] 
                 
Init == 
    /\ TypeInvariant
    /\ viewsPerAd = [r \in Replicas |-> [a \in Ads |-> 0]]
    /\ viewsPerDevice = [r \in Replicas |-> [a \in Ads |-> [d \in Devices|-> 0]]]
    /\ viewsPerDeviceTime = [r \in Replicas |-> [a \in Ads |-> [d \in Devices |-> <<>>]]]
    /\ numLocalOps = [r \in Replicas |-> 0]
    /\ numRemoteOps = [r \in Replicas |-> 0]
    /\ msgs = [r \in Replicas |-> {} ]
    /\ \A a \in Ads : schedule[a].start < schedule[a].end
    /\ \A a \in Ads, d \in Devices: boundsPerDevice[a][d] > 0
    /\ \A a \in Ads, d \in Devices : boundsTotal[a] > boundsPerDevice[a][d]
    /\ \A a \in Ads : schedule[a].start < schedule[a].end
    /\ \A a \in Ads: boundsTotal[a] = sumAll([r \in Replicas |-> stockPerReplica[r][a]])

\* Local operation at replica rep that represents a visualisation of 
\* advert ad in device dv at time t. 
\* Pre: - Advert ad is ongoing; 
\*      - The local state has not exceeded the bounds for advert ad.
\*        Note that in this specification the bounds can be exceeded.
\* Post: - Local views are increased by one; 
\*       - Number of local operations is increased by one;
\*       - operation is propagated to all other replicas.         
LocalInc(rep,ad, dv, t) == 
  LET num == numLocalOps[rep]
      adViews == viewsPerAd[rep][ad]
      deviceViews == viewsPerDevice[rep][ad][dv]
      waiting == msgs[rep]
      remoteOp == [replica |-> rep, adId |-> ad, deviceId |-> dv, time |-> t, order |-> num+1]
  IN /\ replicaOfDevice[dv] = rep
     /\ t >= schedule[ad].start 
     /\ t <= schedule[ad].end
     /\ adViews < stockPerReplica[rep][ad]
     /\ deviceViews < boundsPerDevice[ad][dv]
     /\ viewsPerAd' = [viewsPerAd EXCEPT ![rep][ad] = adViews+1]
     /\ viewsPerDevice' = [viewsPerDevice EXCEPT ![rep][ad][dv] = deviceViews+1]
     /\ viewsPerDeviceTime' = [viewsPerDeviceTime EXCEPT ![rep][ad][dv] = Append(@,t)]
     /\ numLocalOps' = [numLocalOps EXCEPT ![rep] = num+1]
     /\ msgs' = [r \in Replicas |-> IF r = rep THEN waiting ELSE msgs[r] \cup {remoteOp}]
     /\ UNCHANGED <<numRemoteOps,schedule,boundsTotal,boundsPerDevice,stockPerReplica,replicaOfDevice>>

\* Operation that represents a remote execution of an operation at replica rep.
\* Pre: - Selects a remote operation op waiting to be executed, 
\*        that satisfies causal consistency.
\*      - Remote operation preconditions where already verified locally, 
\*        so they should not be verified again.
\* Post: - Local views are updtated; 
\*       - Remote operation is removed from msgs 
RemoteInc(rep) == 
  \E op \in msgs[rep] :
  LET num == op.order
      adViews == viewsPerAd[rep][op.adId]
      deviceViews == viewsPerDevice[rep][op.adId][op.deviceId]
      waiting == msgs[rep]
  IN /\ viewsPerAd' = [viewsPerAd EXCEPT ![rep][op.adId] = adViews+1]
     /\ viewsPerDevice' = [viewsPerDevice EXCEPT ![rep][op.adId][op.deviceId] = deviceViews+1]
     /\ viewsPerDeviceTime' = [viewsPerDeviceTime EXCEPT ![rep][op.adId][op.deviceId] = Append(@,op.time)]
     /\ numRemoteOps' = [numRemoteOps EXCEPT ![rep] = num+1]
     /\ msgs' = [msgs EXCEPT ![rep] = waiting \ {op} ] 
     /\ UNCHANGED <<numLocalOps,schedule,boundsTotal,boundsPerDevice,stockPerReplica,replicaOfDevice>>
       
Consistency == 
/\ \A rep \in Replicas, ad \in Ads, dv \in Devices, t \in Nat: 
            \* A replica does not exceed its stock.
        /\ viewsPerAd[rep][ad] <= stockPerReplica[rep][ad] 
            
            \* Device bounds for an advert are not exceeded.  
        /\ viewsPerDevice[rep][ad][dv] <=  boundsPerDevice[ad][dv]
        
            \* If a device is not assigned to a replica, then its views in that replica
            \* for any advert should be zero 
        /\ replicaOfDevice[dv] /= rep => viewsPerDevice[rep][ad][dv] = 0

            \* All view time stamps for advert ad and device dv are valid.
        /\ \A i \in 1..Len(viewsPerDeviceTime[rep][ad][dv]) : 
                /\ viewsPerDeviceTime[rep][ad][dv][i] >= schedule[ad].start 
                /\ viewsPerDeviceTime[rep][ad][dv][i] <= schedule[ad].end
                
            \* The number of views for advert ad and device dv matches 
            \* the lenght of the time stamps sequence.
        /\ Len(viewsPerDeviceTime[rep][ad][dv]) = viewsPerDevice[rep][ad][dv]
             
            \* The number of views of advert ad matches the summation of 
            \* views in all devices.
        /\ sumAll(viewsPerDevice[rep][ad]) = viewsPerAd[rep][ad]
        
            \* network does not loose messages 
        /\ numLocalOps[rep] + numRemoteOps[rep] + Len(msgs[rep]) = sumAll(numLocalOps)
         
            \* if no messages are waiting then replicas converge
 /\ \A rep1 \in Replicas, rep2 \in Replicas :  msgs[rep1] = {} /\ msgs[rep2] = {} 
        => \A a \in Ads : viewsPerAd[rep1][ad] = viewsPerAd[rep2][ad]
  
Next == \E r \in Replicas, a \in Ads, d \in Devices, t \in Nat : LocalInc(r,a,d,t) \/ RemoteInc(r)
                
vars == <<viewsPerAd,viewsPerDevice,viewsPerDeviceTime,numLocalOps,numRemoteOps,msgs,
            schedule,boundsTotal,boundsPerDevice,stockPerReplica,replicaOfDevice>> 
--------------------------------------------------------------            
Spec == Init /\ [][Next]_vars
--------------------------------------------------------------
THEOREM Spec => TypeInvariant /\ Consistency


=============================================================================
\* Modification History
\* Last modified Mon Sep 01 09:49:27 WEST 2014 by carlaferreira
\* Created Fri Aug 29 07:05:20 WEST 2014 by carlaferreira