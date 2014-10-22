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

\* MV CONSTANT definitions DC
const_1413891214119249000 == 
{dc1, dc2}
----

\* MV CONSTANT definitions DV
const_1413891214131250000 == 
{g1, g2}
----

\* CONSTANT definitions @modelParameterConstants:0deviceAssignment
const_1413891214141251000 == 
[[g \in DV |-> dc1] EXCEPT ![g2] = dc2]
----

\* CONSTANT definitions @modelParameterConstants:1maxTotalViewsPerDC
const_1413891214152252000 == 
[d \in DC |-> 1]
----

\* CONSTANT definitions @modelParameterConstants:4maxTotalViews
const_1413891214163253000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:5maxTotalViewsPerDevice
const_1413891214174254000 == 
[g \in DV |-> 2]
----

\* CONSTANT definition @modelParameterDefinitions:0
def_ov_1413891214186255000 ==
0..2
----
\* CONSTANT definition @modelParameterDefinitions:1
def_ov_1413891214197256000(Replicas) ==
UNION {[Replicas -> Nat]}
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1413891214208257000 ==
Spec
----
=============================================================================
\* Modification History
\* Created Tue Oct 21 12:33:34 WEST 2014 by carlaferreira
