\*Module extending Lifts.tla specification module for use in scope of
\*LiftsExample model (with LiftsExample.cfg configuration).
\*Copyright MyCHIPs.org; See license in root of this package
\* --------------------------------------------------------------------------
\* Extends Lifts.tla specification module with an addition of auxiliary
\* constants and operators which are intended for use in LiftsExample.cfg
\* model configuration. Declares auxiliary constants for all the model values
\* and defines values for all the constant parameters of the specification as
\* auxiliary operators.

---------------------------- MODULE LiftsExample ----------------------------
EXTENDS Lifts, Integers, TLC

CONSTANTS A, B, C, D

UsersValue == {A, B, C, D}
LinksValue == {<<A, B>>, <<B, C>>, <<C, A>>, <<B, D>>}
CyclesValue == {<<A, B, C>>}
PolylinesValue == {<<A, B, D>>}
TransmitTimeValue == {A, B} :> 1..2 @@ {B, C} :> 1..2 @@ {A, C} :> 1..2 @@ {B, D} :> 1..2 @@ {A, D} :> 1..2
InvoiceTimeoutValue == 2
LiftTimeoutValue == 5
TimeLimitValue == 100
PaymentsRangeValue == 1..3
PaymentsCountValue == 8
LinearLiftsCountValue == 4
MaliciousBehaviorFactorValue == 20
=============================================================================
