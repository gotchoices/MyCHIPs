---- MODULE MC ----
EXTENDS RefereeLifts, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
A, B, C, D
----

\* MV CONSTANT definitions Users
const_1600921812032160000 == 
{A, B, C, D}
----

\* CONSTANT definitions @modelParameterConstants:0Links
const_1600921812032161000 == 
{<<A, B>>, <<B, C>>, <<C, A>>, <<B, D>>}
----

\* CONSTANT definitions @modelParameterConstants:2Cycles
const_1600921812032162000 == 
{<<A, B, C>>}
----

\* CONSTANT definitions @modelParameterConstants:3Polylines
const_1600921812032163000 == 
{<<A, B, D>>}
----

\* CONSTANT definitions @modelParameterConstants:4PaymentsCount
const_1600921812032164000 == 
8
----

\* CONSTANT definitions @modelParameterConstants:5PaymentsRange
const_1600921812032165000 == 
1..3
----

\* CONSTANT definitions @modelParameterConstants:6LinearLiftsCount
const_1600921812032166000 == 
4
----

\* CONSTANT definitions @modelParameterConstants:7NewStateLimit
const_1600921812032167000 == 
100
----

\* CONSTANT definitions @modelParameterConstants:8GLOBAL_REF
const_1600921812032168000 == 
"TRUSTED_REF_1"
----

=============================================================================
\* Modification History
\* Created Wed Sep 23 22:30:12 MDT 2020 by kylestorey
