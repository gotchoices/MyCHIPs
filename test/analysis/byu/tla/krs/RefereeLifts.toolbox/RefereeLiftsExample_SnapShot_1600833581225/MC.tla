---- MODULE MC ----
EXTENDS RefereeLifts, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
A, B, C, D
----

\* MV CONSTANT definitions Users
const_160083357715772000 == 
{A, B, C, D}
----

\* CONSTANT definitions @modelParameterConstants:0Links
const_160083357715773000 == 
{<<A, B>>, <<B, C>>, <<C, A>>, <<B, D>>}
----

\* CONSTANT definitions @modelParameterConstants:2Cycles
const_160083357715774000 == 
{<<A, B, C>>}
----

\* CONSTANT definitions @modelParameterConstants:3Polylines
const_160083357715775000 == 
{<<A, B, D>>}
----

\* CONSTANT definitions @modelParameterConstants:4PaymentsCount
const_160083357715776000 == 
8
----

\* CONSTANT definitions @modelParameterConstants:5PaymentsRange
const_160083357715777000 == 
1..3
----

\* CONSTANT definitions @modelParameterConstants:6LinearLiftsCount
const_160083357715778000 == 
4
----

\* CONSTANT definitions @modelParameterConstants:7MaliciousBehaviorFactor
const_160083357715779000 == 
20
----

\* CONSTANT definitions @modelParameterConstants:8NewStateLimit
const_160083357715780000 == 
100
----

\* CONSTANT definitions @modelParameterConstants:9GLOBAL_REF
const_160083357715781000 == 
"TRUSTED_REF_1"
----

=============================================================================
\* Modification History
\* Created Tue Sep 22 21:59:37 MDT 2020 by kylestorey
