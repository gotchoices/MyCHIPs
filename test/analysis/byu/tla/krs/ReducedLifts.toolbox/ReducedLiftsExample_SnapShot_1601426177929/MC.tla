---- MODULE MC ----
EXTENDS ReducedLifts, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
A, B, C, D
----

\* MV CONSTANT definitions Users
const_16014255810802000 == 
{A, B, C, D}
----

\* CONSTANT definitions @modelParameterConstants:0Links
const_16014255810803000 == 
{<<A, B>>, <<B, C>>, <<C, A>>, <<B, D>>}
----

\* CONSTANT definitions @modelParameterConstants:2Cycles
const_16014255810804000 == 
{<<A, B, C>>}
----

\* CONSTANT definitions @modelParameterConstants:3LiftTimeout
const_16014255810805000 == 
5
----

\* CONSTANT definitions @modelParameterConstants:4TimeLimit
const_16014255810806000 == 
100
----

\* CONSTANT definitions @modelParameterConstants:5TransmitTime
const_16014255810807000 == 
{A, B} :> 1..2 @@ {B, C} :> 1..2 @@ {A, C} :> 1..2 @@ {B, D} :> 1..2 @@ {A, D} :> 1..2
----

\* CONSTANT definitions @modelParameterConstants:6InvoiceTimeout
const_16014255810818000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:7Polylines
const_16014255810819000 == 
{<<A, B, D>>}
----

\* CONSTANT definitions @modelParameterConstants:8PaymentsCount
const_160142558108110000 == 
8
----

\* CONSTANT definitions @modelParameterConstants:9PaymentsRange
const_160142558108111000 == 
1..3
----

\* CONSTANT definitions @modelParameterConstants:10LinearLiftsCount
const_160142558108112000 == 
4
----

\* CONSTANT definitions @modelParameterConstants:11MaliciousBehaviorFactor
const_160142558108113000 == 
20
----

=============================================================================
\* Modification History
\* Created Tue Sep 29 18:26:21 MDT 2020 by kylestorey
