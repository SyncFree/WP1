---- MODULE MC ----
EXTENDS adCounterOp, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
dc1, dc2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
g1, g2
----

\* MV CONSTANT definitions DC
const_1413903523031258000 == 
{dc1, dc2}
----

\* MV CONSTANT definitions DV
const_1413903523042259000 == 
{g1, g2}
----

\* CONSTANT definitions @modelParameterConstants:0deviceAssignment
const_1413903523053260000 == 
[[gg \in DV |-> dc1] EXCEPT ![g2] = dc2]
----

\* CONSTANT definitions @modelParameterConstants:1maxTotalViewsPerDC
const_1413903523064261000 == 
[[dc \in DC |-> 1] EXCEPT ![dc2] = 1]
----

\* CONSTANT definitions @modelParameterConstants:4maxTotalViews
const_1413903523075262000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:5maxTotalViewsPerDevice
const_1413903523086263000 == 
[gg \in DV |-> 1]
----

\* CONSTANT definition @modelParameterDefinitions:0
def_ov_1413903523098264000 ==
0..2
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1413903523109265000 ==
Spec
----
=============================================================================
\* Modification History
\* Created Tue Oct 21 15:58:43 WEST 2014 by carlaferreira
