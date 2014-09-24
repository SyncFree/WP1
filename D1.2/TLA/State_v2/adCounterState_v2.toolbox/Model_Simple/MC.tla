---- MODULE MC ----
EXTENDS adCounterState_v2, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
dc1, dc2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
g1, g2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
ad1
----

\* MV CONSTANT definitions DC
const_141138659525875000 == 
{dc1, dc2}
----

\* MV CONSTANT definitions DV
const_141138659526876000 == 
{g1, g2}
----

\* MV CONSTANT definitions AD
const_141138659527977000 == 
{ad1}
----

\* CONSTANT definitions @modelParameterConstants:0deviceAssignment
const_141138659528978000 == 
[[g \in DV |-> dc1] EXCEPT ![g2] = dc2]
----

\* CONSTANT definitions @modelParameterConstants:1maxTotalViewsPerDC
const_141138659529979000 == 
[d \in DC |-> [a \in AD |-> 1]]
----

\* CONSTANT definitions @modelParameterConstants:4maxTotalViews
const_141138659530980000 == 
[a \in AD |-> 2]
----

\* CONSTANT definitions @modelParameterConstants:5maxTotalViewsPerDevice
const_141138659532181000 == 
[a \in AD |-> [g \in DV |-> 2]]
----

\* CONSTANT definition @modelParameterDefinitions:0
def_ov_141138659533282000 ==
0..2
----
\* CONSTANT definition @modelParameterDefinitions:1
def_ov_141138659534283000(Replicas) ==
UNION {[Replicas -> Nat]}
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_141138659535284000 ==
Spec
----
=============================================================================
\* Modification History
\* Created Mon Sep 22 12:49:55 WEST 2014 by carlaferreira
