---- MODULE MC ----
EXTENDS ReducedLifts, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
A, B, C, D
----

\* MV CONSTANT definitions Users
const_160142681513942000 == 
{A, B, C, D}
----

\* CONSTANT definitions @modelParameterConstants:0Links
const_160142681513943000 == 
{<<A, B>>, <<B, C>>, <<C, A>>, <<B, D>>}
----

\* CONSTANT definitions @modelParameterConstants:2Cycles
const_160142681513944000 == 
{<<A, B, C>>}
----

\* CONSTANT definitions @modelParameterConstants:3LiftTimeout
const_160142681513945000 == 
5
----

\* CONSTANT definitions @modelParameterConstants:4TimeLimit
const_160142681513946000 == 
100
----

\* CONSTANT definitions @modelParameterConstants:5TransmitTime
const_160142681513947000 == 
{A, B} :> 1..2 @@ {B, C} :> 1..2 @@ {A, C} :> 1..2 @@ {B, D} :> 1..2 @@ {A, D} :> 1..2
----

\* CONSTANT definitions @modelParameterConstants:6InvoiceTimeout
const_160142681513948000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:7Polylines
const_160142681513949000 == 
{<<A, B, D>>}
----

\* CONSTANT definitions @modelParameterConstants:8PaymentsCount
const_160142681513950000 == 
8
----

\* CONSTANT definitions @modelParameterConstants:9PaymentsRange
const_160142681513951000 == 
1..3
----

\* CONSTANT definitions @modelParameterConstants:10LinearLiftsCount
const_160142681513952000 == 
4
----

\* CONSTANT definitions @modelParameterConstants:11MaliciousBehaviorFactor
const_160142681513953000 == 
20
----

=============================================================================
\* Modification History
\* Created Tue Sep 29 18:46:55 MDT 2020 by kylestorey
