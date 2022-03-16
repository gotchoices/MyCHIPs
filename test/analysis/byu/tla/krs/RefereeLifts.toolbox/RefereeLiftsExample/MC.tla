---- MODULE MC ----
EXTENDS RefereeLifts, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
A, B, C, D
----

\* MV CONSTANT definitions Users
const_1600923015658276000 == 
{A, B, C, D}
----

\* CONSTANT definitions @modelParameterConstants:0Links
const_1600923015658277000 == 
{<<A, B>>, <<B, C>>, <<C, A>>, <<B, D>>}
----

\* CONSTANT definitions @modelParameterConstants:2Cycles
const_1600923015658278000 == 
{<<A, B, C>>}
----

\* CONSTANT definitions @modelParameterConstants:3Polylines
const_1600923015658279000 == 
{<<A, B, D>>}
----

\* CONSTANT definitions @modelParameterConstants:4PaymentsCount
const_1600923015658280000 == 
8
----

\* CONSTANT definitions @modelParameterConstants:5PaymentsRange
const_1600923015658281000 == 
1..3
----

\* CONSTANT definitions @modelParameterConstants:6LinearLiftsCount
const_1600923015658282000 == 
4
----

\* CONSTANT definitions @modelParameterConstants:7NewStateLimit
const_1600923015658283000 == 
100
----

\* CONSTANT definitions @modelParameterConstants:8GLOBAL_REF
const_1600923015658284000 == 
"TRUSTED_REF_1"
----

\* INIT definition @modelBehaviorInit:0
init_1600923015658285000 ==
/\  _stateNum = 1
/\  lifts = (A :> << >> @@ B :> << >> @@ C :> << >> @@ D :> << >>)
/\  linearLiftsRemaining = 4
/\  messages = << >>
/\  nextGuid = 101
/\  paymentsRemaining = 8
/\  tallies = ( <<A, B, "Foil">> :> [chits |-> <<>>] @@
  <<A, C, "Stock">> :> [chits |-> <<>>] @@
  <<B, A, "Stock">> :> [chits |-> <<>>] @@
  <<B, C, "Foil">> :> [chits |-> <<>>] @@
  <<B, D, "Foil">> :> [chits |-> <<>>] @@
  <<C, A, "Foil">> :> [chits |-> <<>>] @@
  <<C, B, "Stock">> :> [chits |-> <<>>] @@
  <<D, B, "Stock">> :> [chits |-> <<>>] )
----
=============================================================================
\* Modification History
\* Created Wed Sep 23 22:50:15 MDT 2020 by kylestorey
