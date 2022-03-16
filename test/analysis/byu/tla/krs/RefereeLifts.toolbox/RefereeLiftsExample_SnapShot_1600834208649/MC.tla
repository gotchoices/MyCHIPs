---- MODULE MC ----
EXTENDS RefereeLifts, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
A, B, C, D
----

\* MV CONSTANT definitions Users
const_1600834204787108000 == 
{A, B, C, D}
----

\* CONSTANT definitions @modelParameterConstants:0Links
const_1600834204787109000 == 
{<<A, B>>, <<B, C>>, <<C, A>>, <<B, D>>}
----

\* CONSTANT definitions @modelParameterConstants:2Cycles
const_1600834204787110000 == 
{<<A, B, C>>}
----

\* CONSTANT definitions @modelParameterConstants:3Polylines
const_1600834204787111000 == 
{<<A, B, D>>}
----

\* CONSTANT definitions @modelParameterConstants:4PaymentsCount
const_1600834204788112000 == 
8
----

\* CONSTANT definitions @modelParameterConstants:5PaymentsRange
const_1600834204788113000 == 
1..3
----

\* CONSTANT definitions @modelParameterConstants:6LinearLiftsCount
const_1600834204788114000 == 
4
----

\* CONSTANT definitions @modelParameterConstants:7MaliciousBehaviorFactor
const_1600834204788115000 == 
20
----

\* CONSTANT definitions @modelParameterConstants:8NewStateLimit
const_1600834204788116000 == 
100
----

\* CONSTANT definitions @modelParameterConstants:9GLOBAL_REF
const_1600834204788117000 == 
"TRUSTED_REF_1"
----

=============================================================================
\* Modification History
\* Created Tue Sep 22 22:10:04 MDT 2020 by kylestorey
