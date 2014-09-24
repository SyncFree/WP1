---- MODULE MC ----
EXTENDS adCounterState_v0, TLC

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
const_141103555339783000 == 
{dc1, dc2}
----

\* MV CONSTANT definitions DV
const_141103555340884000 == 
{g1, g2}
----

\* MV CONSTANT definitions AD
const_141103555341985000 == 
{ad1}
----

\* CONSTANT definitions @modelParameterConstants:0deviceAssignment
const_141103555343086000 == 
g1 :> dc1 @@Êg2 :> dc2
----

\* CONSTANT definitions @modelParameterConstants:1maxTotalViewsPerDC
const_141103555344187000 == 
[d \in DC |-> [a \in AD |-> 1]]
----

\* CONSTANT definitions @modelParameterConstants:4maxTotalViews
const_141103555345288000 == 
[a \in AD |-> 2]
----

\* CONSTANT definitions @modelParameterConstants:5maxTotalViewsPerDevice
const_141103555346789000 == 
[a \in AD |-> [g \in DV |-> 2]]
----

\* CONSTANT definition @modelParameterDefinitions:0
def_ov_141103555347890000 ==
0..2
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_141103555348991000 ==
Spec
----
=============================================================================
\* Modification History
\* Created Thu Sep 18 11:19:13 WEST 2014 by carlaferreira
