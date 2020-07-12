\*MyCHIPs payments and lifts specification module.
\*Copyright MyCHIPs.org; See license in root of this package
\* -------------------------------------------------------------------------
\* Specifies voluntary payments, payments of invoices, circular and linear
\* lifts. Assumes that each user is hosted at its individual site. Includes
\* an example of malicious behavior when at the lift proposal phase
\* a non-originator user reduces (in magnitude) the value in the pending
\* chit being added to their stock tally and sends the query/terminus
\* message with this reduced value to the foil peer.

------------------------------- MODULE Lifts -------------------------------

EXTENDS Integers, Sequences, FiniteSets, Bags, TLC

CONSTANTS
    Users,
    Links,
    Cycles,
    Polylines,
    TransmitTime,
    InvoiceTimeout,
    LiftTimeout,
    TimeLimit,
    PaymentsRange,
    PaymentsCount,
    LinearLiftsCount,
    MaliciousBehaviorFactor

ASSUME
    /\ Links \subseteq Users \X Users
    /\ \A link \in Links: link[1] # link[2]

NextIndexIn(i, ring) == (i % Len(ring)) + 1

PrevIndexIn(i, ring) == ((i - 2) % Len(ring)) + 1

ASSUME \A cycle \in Cycles:
    /\ \A i \in 1..Len(cycle): cycle[i] \in Users
    /\ \A i, j \in 1..Len(cycle): i # j => cycle[i] # cycle[j]
    /\ \A i \in 1..Len(cycle): <<cycle[i], cycle[NextIndexIn(i, cycle)]>> \in Links

ASSUME \A polyline \in Polylines:
    /\ \A i \in 1..Len(polyline): polyline[i] \in Users
    /\ \A i, j \in 1..Len(polyline): i # j => polyline[i] # polyline[j]
    /\ \A i \in 1..(Len(polyline) - 1): <<polyline[i], polyline[i + 1]>> \in Links
    /\ <<polyline[Len(polyline)], polyline[1]>> \notin Links

ASSUME TransmitTime \in
    [{{a, b}: <<a, b>> \in
        {<<x, y>> \in Users \X Users:
            \/ <<x, y>> \in Links
            \/ \E polyline \in Polylines: x = polyline[Len(polyline)] /\ y = polyline[1]
        }
     } ->
     {range \in SUBSET Int: \E min, max \in 0..99: min <= max /\ range = min..max}]

ASSUME InvoiceTimeout \in Nat

ASSUME LiftTimeout \in Nat

ASSUME TimeLimit \in Nat

ASSUME PaymentsRange \in {range \in SUBSET Nat: \E min, max \in 1..999: min <= max /\ range = min..max}

ASSUME PaymentsCount \in Int

ASSUME
    /\ LinearLiftsCount \in Int
    /\ LinearLiftsCount >= 0

ASSUME MaliciousBehaviorFactor \in 0..100

VARIABLES
    tallies,
    lifts,
    messages,
    paymentsRemaining,
    linearLiftsRemaining,
    nextGuid,
    now,
    _stateNum

vars == <<tallies, lifts, messages, paymentsRemaining, linearLiftsRemaining, nextGuid, now, _stateNum>>

\* Tally types
Foil == "Foil"
Stock == "Stock"

\* Lift types
Circular == "Circular"
Linear == "Linear"

\* Chit states
Invoiced == "Invoiced"
Pend == "Pend"
Good == "Good"
Failed == "Failed"
Timeout == "Timeout"

\* Lift states
Seek == "Seek"
\* Pend == "Pend" - already defined in Chit states section
\* Good == "Good" - already defined in Chit states section
\* Failed == "Failed" - already defined in Chit states section
\* Timeout == "Timeout" - already defined in Chit states section

\* Chit types
PaymentType == "PaymentType"
LiftType == "LiftType"

\* Message types
ChitJson == "ChitJson"
LiftJson == "LiftJson"

\* ChitJson actions
PeerInvoice == "PeerInvoice"
PeerValid == "PeerValid"
PeerDecline == "PeerDecline"

\* LiftJson actions
Query == "Query"
Terminus == "Terminus"
\* Timeout == "Timeout" - already defined in Chit states section
Fail == "Fail"
Commit == "Commit"

NextElemIn(elem, ring) ==
    LET I == CHOOSE i \in 1..Len(ring): ring[i] = elem
    IN ring[NextIndexIn(I, ring)]

PrevElemIn(elem, ring) ==
    LET I == CHOOSE i \in 1..Len(ring): ring[i] = elem
    IN ring[PrevIndexIn(I, ring)]

RECURSIVE Sum(_)
Sum(f) ==
    IF DOMAIN f = {} THEN
        0
    ELSE
        LET X == CHOOSE x \in DOMAIN f: TRUE
        IN f[X] + Sum([y \in DOMAIN f \ {X} |-> f[y]])

Opposite(tallyType) ==
    CASE tallyType = Foil -> Stock
    [] tallyType = Stock -> Foil

TalliesOfType(type) == [id \in {id \in DOMAIN tallies: id[3] = type} |-> tallies[id]]

FoilTallies == TalliesOfType(Foil)
StockTallies == TalliesOfType(Stock)

ProjectedBalance(tally) ==
    LET ValidChitIndexes == {i \in DOMAIN tally.chits: tally.chits[i].state \in {Good, Pend}}
    IN Sum([i \in ValidChitIndexes |-> tally.chits[i].value])

FoilsProjectedBalances == [id \in DOMAIN FoilTallies |-> ProjectedBalance(tallies[id])]
StocksProjectedBalances == [id \in DOMAIN StockTallies |-> ProjectedBalance(tallies[id])]

AvailableBalance(tally) ==
    LET GoodChitIndexes == {i \in DOMAIN tally.chits: tally.chits[i].state = Good}
    IN Sum([i \in GoodChitIndexes |-> tally.chits[i].value])

FoilAvailableBalances == [id \in DOMAIN FoilTallies |-> AvailableBalance(tallies[id])]
StocksAvailableBalances == [id \in DOMAIN StockTallies |-> AvailableBalance(tallies[id])]

AddChit(tally, chit) == [tally EXCEPT !.chits = Append(@, chit)]

UpdateChit(tally, chitType, guidFieldName, guid, state) ==
    [tally EXCEPT !.chits =
        [i \in DOMAIN tally.chits |->
            [tally.chits[i] EXCEPT !.state =
                IF
                    /\ tally.chits[i].type = chitType
                    /\ tally.chits[i][guidFieldName] = guid
                THEN
                    state
                ELSE
                    tally.chits[i].state]]]

UpdateLiftChit(tally, liftGuid, state) == UpdateChit(tally, LiftType, "liftGuid", liftGuid, state)

UpdatePaymentChit(tally, paymentGuid, state) == UpdateChit(tally, PaymentType, "paymentGuid", paymentGuid, state)

Message(msg) == msg @@ "rcvTimer" :> RandomElement(TransmitTime[{msg.from, msg.to}])

Values(f) == {f[x]: x \in DOMAIN f}

Min(s) == CHOOSE x \in s: \A y \in s: y >= x

Max(s) == CHOOSE x \in s: \A y \in s: y <= x

MaxLiftValueFor(route, balance(_)) == Min(
    Values([stockId \in {id \in DOMAIN tallies:
        \E i \in DOMAIN route: <<route[i], route[PrevIndexIn(i, route)], Stock>> = id}
            |-> balance(tallies[stockId])]) \union
    Values([foilId \in {id \in DOMAIN tallies:
        \E i \in DOMAIN route: <<route[i], route[NextIndexIn(i, route)], Foil>> = id}
            |-> -balance(tallies[foilId])]))

(*** Initial State ***)

Init ==
    /\ tallies = [id \in UNION {{<<x, y, Foil>>, <<y, x, Stock>>}: <<x, y>> \in Links} |-> [chits |-> <<>>]]
    /\ lifts = [user \in Users |-> [liftGuid \in {} |-> 0]]
    /\ messages = EmptyBag
    /\ paymentsRemaining = PaymentsCount
    /\ linearLiftsRemaining = LinearLiftsCount
    /\ nextGuid = 101
    /\ now = 0
    /\ _stateNum = 1
    /\ Print("Init", _stateNum) = 1

(*** Voluntary Payment ***)

SendPayment ==
    /\ paymentsRemaining > 0
    /\ \E <<foil, stock, type>> \in DOMAIN FoilTallies:
        /\ tallies' = [tallies EXCEPT ![<<foil, stock, Foil>>] =
            AddChit(@, [value |-> -RandomElement(PaymentsRange), type |-> PaymentType, paymentGuid |-> nextGuid, state |-> Good])]
        /\
            LET
                Chits == tallies'[<<foil, stock, Foil>>].chits
                NewChit == Chits[Len(Chits)]
            IN
                messages' = messages
                    (+) SetToBag({Message(
                        [from |-> foil, to |-> stock, type |-> ChitJson, action |-> PeerValid, paymentGuid |-> nextGuid, value |-> -NewChit.value])})
        /\ nextGuid' = nextGuid + 1
        /\ paymentsRemaining' = paymentsRemaining - 1
    /\ UNCHANGED <<lifts, linearLiftsRemaining, now>>
    /\ _stateNum' = Print("SendPayment", _stateNum + 1)

ReceivePayment ==
    /\ \E msg \in BagToSet(messages):
        /\ msg.rcvTimer <= 0
        /\ msg.type = ChitJson
        /\ msg.action = PeerValid
        /\
            LET Tally == tallies[<<msg.to, msg.from, Stock>>]
            IN
                ~\E i \in DOMAIN Tally.chits:
                    /\ Tally.chits[i].type = PaymentType
                    /\ Tally.chits[i].paymentGuid = msg.paymentGuid
        /\ tallies' = [tallies EXCEPT ![<<msg.to, msg.from, Stock>>] =
            AddChit(@, [value |-> msg.value, type |-> PaymentType, paymentGuid |-> msg.paymentGuid, state |-> Good])]
        /\ messages' = messages (-) SetToBag({msg})
    /\ UNCHANGED <<lifts, paymentsRemaining, linearLiftsRemaining, nextGuid, now>>
    /\ _stateNum' = Print("ReceivePayment", _stateNum + 1)

(*** Payment of Invoice ***)

SendInvoice ==
    /\ paymentsRemaining > 0
    /\ \E <<stock, foil, type>> \in DOMAIN StockTallies:
        /\ tallies' = [tallies EXCEPT ![<<stock, foil, Stock>>] =
            AddChit(@, [value |-> RandomElement(PaymentsRange), type |-> PaymentType, paymentGuid |-> nextGuid, expire |-> now + InvoiceTimeout, state |-> Invoiced])]
        /\
            LET
                Chits == tallies'[<<stock, foil, Stock>>].chits
                NewChit == Chits[Len(Chits)]
            IN
                messages' = messages
                    (+) SetToBag({Message(
                        [from |-> stock, to |-> foil, type |-> ChitJson, action |-> PeerInvoice,
                        paymentGuid |-> nextGuid, value |-> NewChit.value, expire |-> now + InvoiceTimeout])})
        /\ nextGuid' = nextGuid + 1
        /\ paymentsRemaining' = paymentsRemaining - 1
    /\ UNCHANGED <<lifts, linearLiftsRemaining, now>>
    /\ _stateNum' = Print("SendInvoice", _stateNum + 1)

PayInvoice ==
    /\ \E msg \in BagToSet(messages):
        /\ msg.rcvTimer <= 0
        /\ msg.type = ChitJson
        /\ msg.action = PeerInvoice
        /\
            LET Tally == tallies[<<msg.to, msg.from, Foil>>]
            IN
                ~\E i \in DOMAIN Tally.chits:
                    /\ Tally.chits[i].type = PaymentType
                    /\ Tally.chits[i].paymentGuid = msg.paymentGuid
        /\ tallies' = [tallies EXCEPT ![<<msg.to, msg.from, Foil>>] =
            AddChit(@, [value |-> -msg.value, type |-> PaymentType, paymentGuid |-> msg.paymentGuid, expire |-> msg.expire, state |-> Good])]
        /\ messages' = messages
            (-) SetToBag({msg})
            (+) SetToBag({Message(
                [from |-> msg.to, to |-> msg.from, type |-> ChitJson, action |-> PeerValid,
                paymentGuid |-> msg.paymentGuid, value |-> msg.value, expire |-> msg.expire])})
    /\ UNCHANGED <<lifts, paymentsRemaining, linearLiftsRemaining, nextGuid, now>>
    /\ _stateNum' = Print("PayInvoice", _stateNum + 1)

DeclineInvoice ==
    /\ \E msg \in BagToSet(messages):
        /\ msg.rcvTimer <= 0
        /\ msg.type = ChitJson
        /\ msg.action = PeerInvoice
        /\
            LET Tally == tallies[<<msg.to, msg.from, Foil>>]
            IN
                ~\E i \in DOMAIN Tally.chits:
                    /\ Tally.chits[i].type = PaymentType
                    /\ Tally.chits[i].paymentGuid = msg.paymentGuid
        /\ tallies' = [tallies EXCEPT ![<<msg.to, msg.from, Foil>>] =
            AddChit(@, [value |-> -msg.value, type |-> PaymentType, paymentGuid |-> msg.paymentGuid, expire |-> msg.expire, state |-> Failed])]
        /\ messages' = messages
            (-) SetToBag({msg})
            (+) SetToBag({Message(
                [from |-> msg.to, to |-> msg.from, type |-> ChitJson, action |-> PeerDecline,
                paymentGuid |-> msg.paymentGuid, value |-> msg.value, expire |-> msg.expire])})
    /\ UNCHANGED <<lifts, paymentsRemaining, linearLiftsRemaining, nextGuid, now>>
    /\ _stateNum' = Print("DeclineInvoice", _stateNum + 1)

ReceivePaidInvoice ==
    /\ \E msg \in BagToSet(messages):
        /\ msg.rcvTimer <= 0
        /\ msg.type = ChitJson
        /\ msg.action = PeerValid
        /\
            LET Tally == tallies[<<msg.to, msg.from, Stock>>]
            IN
                \E i \in DOMAIN Tally.chits:
                    /\ Tally.chits[i].type = PaymentType
                    /\ Tally.chits[i].paymentGuid = msg.paymentGuid
                    /\ Tally.chits[i].state \in {Invoiced, Timeout}
                    /\ msg.value = Tally.chits[i].value
                    /\ msg.expire = Tally.chits[i].expire
        /\ tallies' = [tallies EXCEPT ![<<msg.to, msg.from, Stock>>] = UpdatePaymentChit(@, msg.paymentGuid, Good)]
        /\ messages' = messages (-) SetToBag({msg})
    /\ UNCHANGED <<lifts, paymentsRemaining, linearLiftsRemaining, nextGuid, now>>
    /\ _stateNum' = Print("ReceivePaidInvoice", _stateNum + 1)

ReceiveDeclinedInvoice ==
    /\ \E msg \in BagToSet(messages):
        /\ msg.rcvTimer <= 0
        /\ msg.type = ChitJson
        /\ msg.action = PeerDecline
        /\
            LET Tally == tallies[<<msg.to, msg.from, Stock>>]
            IN
                \E i \in DOMAIN Tally.chits:
                    /\ Tally.chits[i].type = PaymentType
                    /\ Tally.chits[i].paymentGuid = msg.paymentGuid
                    /\ Tally.chits[i].state \in {Invoiced, Timeout}
                    /\ msg.value = Tally.chits[i].value
                    /\ msg.expire = Tally.chits[i].expire
        /\ tallies' = [tallies EXCEPT ![<<msg.to, msg.from, Stock>>] = UpdatePaymentChit(@, msg.paymentGuid, Failed)]
        /\ messages' = messages (-) SetToBag({msg})
    /\ UNCHANGED <<lifts, paymentsRemaining, linearLiftsRemaining, nextGuid, now>>
    /\ _stateNum' = Print("ReceiveDeclinedInvoice", _stateNum + 1)

TimeOutInvoice ==
    \E id \in DOMAIN StockTallies: \E i \in DOMAIN tallies[id].chits:
        LET Chit == tallies[id].chits[i]
        IN
            /\ Chit.type = PaymentType
            /\ Chit.state = Invoiced
            /\ now >= Chit.expire
        /\ tallies' = [tallies EXCEPT ![id] = UpdatePaymentChit(@, tallies[id].chits[i].paymentGuid, Timeout)]
    /\ UNCHANGED <<lifts, messages, paymentsRemaining, linearLiftsRemaining, nextGuid, now>>
    /\ _stateNum' = Print("TimeOutInvoice", _stateNum + 1)

(*** Lift Proposal (Upstream) ***)

ProposeLift(route, liftType, value) ==
    /\
        LET
            User == route[Len(route)]
            FoilPeer == PrevElemIn(User, route)
            StockPeer == NextElemIn(User, route)
        IN
            /\ lifts' = [lifts EXCEPT ![User] =
                nextGuid :> [route |-> route, liftType |-> liftType, originator |-> User, destination |-> StockPeer,
                    value |-> value, expire |-> now + LiftTimeout, state |-> Seek] @@ @]
            /\
                LET NewLift == lifts'[User][nextGuid]
                IN
                    /\ tallies' =
                        [id \in DOMAIN tallies |->
                            CASE id = <<User, FoilPeer, Stock>> ->
                                AddChit(tallies[id], [value |-> -NewLift.value, state |-> Pend, type |-> LiftType, liftGuid |-> nextGuid])
                            [] id = <<User, StockPeer, Foil>> ->
                                AddChit(tallies[id], [value |-> NewLift.value, state |-> Pend, type |-> LiftType, liftGuid |-> nextGuid])
                            [] OTHER ->
                                tallies[id]]
                    /\ messages' = messages
                        (+) SetToBag({Message(
                            [from |-> User, to |-> FoilPeer, type |-> LiftJson, action |-> Query, liftGuid |-> nextGuid,
                            route |-> NewLift.route, liftType |-> NewLift.liftType, originator |-> NewLift.originator,
                            destination |-> NewLift.destination, value |-> NewLift.value, expire |-> NewLift.expire])})
            /\ nextGuid' = nextGuid + 1
    /\ UNCHANGED <<paymentsRemaining, now>>

ProposeCircularLift ==
    /\ \E cycle \in Cycles:
        LET MaxLiftValue == MaxLiftValueFor(cycle, ProjectedBalance)
        IN
            /\ MaxLiftValue > 0
            /\ \E i \in DOMAIN cycle:
                LET Route == [j \in DOMAIN cycle |-> cycle[((j - 1 + i) % Len(cycle)) + 1]]
                IN ProposeLift(Route, Circular, RandomElement(1..MaxLiftValue))
    /\ UNCHANGED <<linearLiftsRemaining>>
    /\ _stateNum' = Print("ProposeCircularLift", _stateNum + 1)

ProposeLinearLift ==
    /\ linearLiftsRemaining > 0
    /\ \E route \in Polylines:
        LET MaxLiftValue == MaxLiftValueFor(route, ProjectedBalance)
        IN
            /\ MaxLiftValue > 0
            /\ ProposeLift(route, Linear, RandomElement(1..MaxLiftValue))
            /\ linearLiftsRemaining' = linearLiftsRemaining - 1
    /\ _stateNum' = Print("ProposeLinearLift", _stateNum + 1)

HandleLiftProposal ==
    /\ \E msg \in BagToSet(messages):
        /\ msg.rcvTimer <= 0
        /\ msg.type = LiftJson
        /\ msg.action = Query
        /\ msg.liftGuid \notin DOMAIN lifts[msg.to]
        /\
            LET
                User == msg.to
                FoilPeer == PrevElemIn(User, msg.route)
                StockPeer == NextElemIn(User, msg.route)
            IN
                /\ msg.from = StockPeer
                /\ User # msg.originator
                /\ <<User, FoilPeer, Stock>> \in DOMAIN tallies => ProjectedBalance(tallies[<<User, FoilPeer, Stock>>]) - msg.value >= 0
                /\ <<User, StockPeer, Foil>> \in DOMAIN tallies => ProjectedBalance(tallies[<<User, StockPeer, Foil>>]) + msg.value <= 0
                /\ lifts' = [lifts EXCEPT ![User] =
                    msg.liftGuid :> [route |-> msg.route, liftType |-> msg.liftType, originator |-> msg.originator,
                        destination |-> msg.destination, value |-> msg.value, expire |-> msg.expire, state |-> Pend] @@ @]
                /\ tallies' =
                    [id \in DOMAIN tallies |->
                        CASE id = <<User, FoilPeer, Stock>> ->
                            AddChit(tallies[id], [value |-> -msg.value, state |-> Pend, type |-> LiftType, liftGuid |-> msg.liftGuid])
                        [] id = <<User, StockPeer, Foil>> ->
                            AddChit(tallies[id], [value |-> msg.value, state |-> Pend, type |-> LiftType, liftGuid |-> msg.liftGuid])
                        [] OTHER ->
                            tallies[id]]
                /\ messages' = messages
                    (-) SetToBag({msg})
                    (+) SetToBag({Message(
                        [from |-> User, to |-> FoilPeer, type |-> LiftJson, action |-> IF User = msg.destination THEN Terminus ELSE Query,
                        liftGuid |-> msg.liftGuid, route |-> msg.route, liftType |-> msg.liftType, originator |-> msg.originator,
                        destination |-> msg.destination, value |-> msg.value, expire |-> msg.expire])})
    /\ UNCHANGED <<paymentsRemaining, linearLiftsRemaining, nextGuid, now>>
    /\ _stateNum' = Print("HandleLiftProposal", _stateNum + 1)

MaliciouslyHandleLiftProposal ==
    /\ RandomElement(1..100) <= MaliciousBehaviorFactor
    /\ \E msg \in BagToSet(messages):
        /\ msg.rcvTimer <= 0
        /\ msg.type = LiftJson
        /\ msg.action = Query
        /\ msg.liftGuid \notin DOMAIN lifts[msg.to]
        /\
            LET
                User == msg.to
                FoilPeer == PrevElemIn(User, msg.route)
                StockPeer == NextElemIn(User, msg.route)
            IN
                /\ msg.from = StockPeer
                /\ User # msg.originator
                /\ User = msg.destination => <<User, FoilPeer, Stock>> \in DOMAIN tallies
                /\ msg.value > 1
                /\ <<User, FoilPeer, Stock>> \in DOMAIN tallies => ProjectedBalance(tallies[<<User, FoilPeer, Stock>>]) - (msg.value - 1) >= 0
                /\ <<User, StockPeer, Foil>> \in DOMAIN tallies => ProjectedBalance(tallies[<<User, StockPeer, Foil>>]) + msg.value <= 0
                /\ lifts' = [lifts EXCEPT ![User] =
                    msg.liftGuid :> [route |-> msg.route, liftType |-> msg.liftType, originator |-> msg.originator,
                        destination |-> msg.destination, value |-> msg.value, expire |-> msg.expire, state |-> Pend] @@ @]
                /\ tallies' =
                    [id \in DOMAIN tallies |->
                        CASE id = <<User, FoilPeer, Stock>> ->
                            AddChit(tallies[id], [value |-> -(msg.value - 1), state |-> Pend, type |-> LiftType, liftGuid |-> msg.liftGuid])
                        [] id = <<User, StockPeer, Foil>> ->
                            AddChit(tallies[id], [value |-> msg.value, state |-> Pend, type |-> LiftType, liftGuid |-> msg.liftGuid])
                        [] OTHER ->
                            tallies[id]]
                /\ messages' = messages
                    (-) SetToBag({msg})
                    (+) SetToBag({Message(
                        [from |-> User, to |-> FoilPeer, type |-> LiftJson, action |-> IF User = msg.destination THEN Terminus ELSE Query,
                        liftGuid |-> msg.liftGuid, route |-> msg.route, liftType |-> msg.liftType, originator |-> msg.originator,
                        destination |-> msg.destination, value |-> msg.value - 1, expire |-> msg.expire])})
    /\ UNCHANGED <<paymentsRemaining, linearLiftsRemaining, nextGuid, now>>
    /\ _stateNum' = Print("MaliciouslyHandleLiftProposal", _stateNum + 1)

IgnoreTimedOutLiftProposal ==
    /\ \E msg \in BagToSet(messages):
        /\ msg.rcvTimer <= 0
        /\ msg.type = LiftJson
        /\ msg.action = Query
        /\ msg.liftGuid \in DOMAIN lifts[msg.to]
        /\
            LET
                User == msg.to
                Lift == lifts[User][msg.liftGuid]
                StockPeer == NextElemIn(User, Lift.route)
            IN
                /\ msg.from = StockPeer
                /\ User # Lift.originator
                /\ Lift.state = Timeout
                /\ messages' = messages (-) SetToBag({msg})
    /\ UNCHANGED <<tallies, lifts, paymentsRemaining, linearLiftsRemaining, nextGuid, now>>
    /\ _stateNum' = Print("IgnoreTimedOutLiftProposal", _stateNum + 1)

IgnoreTimedOutLiftTerminus ==
    /\ \E msg \in BagToSet(messages):
        /\ msg.rcvTimer <= 0
        /\ msg.type = LiftJson
        /\ msg.action = Terminus
        /\
            LET
                User == msg.to
                Lift == lifts[User][msg.liftGuid]
                StockPeer == NextElemIn(User, Lift.route)
            IN
                /\ msg.from = StockPeer
                /\ msg.from = Lift.destination
                /\ User = Lift.originator
                /\ Lift.state = Timeout
                /\ messages' = messages (-) SetToBag({msg})
    /\ UNCHANGED <<tallies, lifts, paymentsRemaining, linearLiftsRemaining, nextGuid, now>>
    /\ _stateNum' = Print("IgnoreTimedOutLiftTerminus", _stateNum + 1)

(*** Lift Timeout (Upstream) ***)

TimeOutLift ==
    \E user \in Users: \E liftGuid \in DOMAIN lifts[user]:
        LET Lift == lifts[user][liftGuid]
        IN
            /\ Lift.state = Seek
            /\ now >= Lift.expire
            /\
                LET
                    FoilPeer == PrevElemIn(user, Lift.route)
                    StockPeer == NextElemIn(user, Lift.route)
                IN
                    /\ lifts' = [lifts EXCEPT ![user] = [@ EXCEPT ![liftGuid] = [@ EXCEPT !.state = Timeout]]]
                    /\ tallies' =
                        [id \in DOMAIN tallies |->
                            CASE id = <<user, FoilPeer, Stock>> -> UpdateLiftChit(tallies[id], liftGuid, Timeout)
                            [] id = <<user, StockPeer, Foil>> -> UpdateLiftChit(tallies[id], liftGuid, Timeout)
                            [] OTHER -> tallies[id]]
                    /\ messages' = messages
                        (+) SetToBag({Message(
                            [from |-> user, to |-> FoilPeer, type |-> LiftJson, action |-> Timeout, liftGuid |-> liftGuid,
                            route |-> Lift.route, liftType |-> Lift.liftType, originator |-> Lift.originator,
                            destination |-> Lift.destination, value |-> Lift.value, expire |-> Lift.expire])})
    /\ UNCHANGED <<paymentsRemaining, linearLiftsRemaining, nextGuid, now>>
    /\ _stateNum' = Print("TimeOutLift", _stateNum + 1)

HandleLiftTimeout ==
    /\ \E msg \in BagToSet(messages):
        /\ msg.rcvTimer <= 0
        /\ msg.type = LiftJson
        /\ msg.action = Timeout
        /\ msg.liftGuid \in DOMAIN lifts[msg.to]
        /\
            LET
                User == msg.to
                Lift == lifts[User][msg.liftGuid]
                FoilPeer == PrevElemIn(User, Lift.route)
                StockPeer == NextElemIn(User, Lift.route)
            IN
                /\ msg.from = StockPeer
                /\ User # Lift.originator
                /\ Lift.state = Pend
                /\ lifts' = [lifts EXCEPT ![User] = [@ EXCEPT ![msg.liftGuid] = [@ EXCEPT !.state = Timeout]]]
                /\ tallies' =
                    [id \in DOMAIN tallies |->
                        CASE id = <<User, FoilPeer, Stock>> -> UpdateLiftChit(tallies[id], msg.liftGuid, Timeout)
                        [] id = <<User, StockPeer, Foil>> -> UpdateLiftChit(tallies[id], msg.liftGuid, Timeout)
                        [] OTHER -> tallies[id]]
                /\ messages' = messages
                    (-) SetToBag({msg})
                    (+) SetToBag({Message(
                        [from |-> User, to |-> FoilPeer, type |-> LiftJson, action |-> Timeout, liftGuid |-> msg.liftGuid,
                        route |-> msg.route, liftType |-> msg.liftType, originator |-> msg.originator,
                        destination |-> msg.destination, value |-> msg.value, expire |-> msg.expire])})
    /\ UNCHANGED <<paymentsRemaining, linearLiftsRemaining, nextGuid, now>>
    /\ _stateNum' = Print("HandleLiftTimeout", _stateNum + 1)

HandleUnknownLiftTimeout ==
    /\ \E msg \in BagToSet(messages):
        /\ msg.rcvTimer <= 0
        /\ msg.type = LiftJson
        /\ msg.action = Timeout
        /\ msg.liftGuid \notin DOMAIN lifts[msg.to]
        /\
            LET
                User == msg.to
                FoilPeer == PrevElemIn(User, msg.route)
                StockPeer == NextElemIn(User, msg.route)
            IN
                /\ msg.from = StockPeer
                /\ User # msg.originator
                /\ lifts' = [lifts EXCEPT ![User] =
                    msg.liftGuid :> [route |-> msg.route, liftType |-> msg.liftType, originator |-> msg.originator,
                        destination |-> msg.destination, value |-> msg.value, expire |-> msg.expire, state |-> Timeout] @@ @]
                /\ messages' = messages
                    (-) SetToBag({msg})
                    (+) SetToBag({Message(
                        [from |-> User, to |-> FoilPeer, type |-> LiftJson, action |-> Timeout, liftGuid |-> msg.liftGuid,
                        route |-> msg.route, liftType |-> msg.liftType, originator |-> msg.originator,
                        destination |-> msg.destination, value |-> msg.value, expire |-> msg.expire])})
    /\ UNCHANGED <<tallies, paymentsRemaining, linearLiftsRemaining, nextGuid, now>>
    /\ _stateNum' = Print("HandleUnknownLiftTimeout", _stateNum + 1)

HandleLiftTimeoutLoopback ==
    /\ \E msg \in BagToSet(messages):
        /\ msg.rcvTimer <= 0
        /\ msg.type = LiftJson
        /\ msg.action = Timeout
        /\ msg.liftGuid \in DOMAIN lifts[msg.to]
        /\
            LET
                User == msg.to
                Lift == lifts[User][msg.liftGuid]
                StockPeer == NextElemIn(User, Lift.route)
            IN
                /\ msg.from = StockPeer
                /\ msg.from = Lift.destination
                /\ User = Lift.originator
                /\ Lift.state = Timeout
                /\ messages' = messages (-) SetToBag({msg})
    /\ UNCHANGED <<tallies, lifts, paymentsRemaining, linearLiftsRemaining, nextGuid, now>>
    /\ _stateNum' = Print("HandleLiftTimeoutLoopback", _stateNum + 1)

IgnoreFailedLiftTimeout ==
    /\ \E msg \in BagToSet(messages):
        /\ msg.rcvTimer <= 0
        /\ msg.type = LiftJson
        /\ msg.action = Timeout
        /\ msg.liftGuid \in DOMAIN lifts[msg.to]
        /\
            LET
                User == msg.to
                Lift == lifts[User][msg.liftGuid]
                StockPeer == NextElemIn(User, Lift.route)
            IN
                /\ msg.from = StockPeer
                /\ User # Lift.originator
                /\ Lift.state = Failed
                /\ messages' = messages (-) SetToBag({msg})
    /\ UNCHANGED <<tallies, lifts, paymentsRemaining, linearLiftsRemaining, nextGuid, now>>
    /\ _stateNum' = Print("IgnoreFailedLiftTimeout", _stateNum + 1)

(*** Lift Fail (Downstream) ***)

FailExceedingLiftProposal ==
    /\ \E msg \in BagToSet(messages):
        /\ msg.rcvTimer <= 0
        /\ msg.type = LiftJson
        /\ msg.action = Query
        /\ msg.liftGuid \notin DOMAIN lifts[msg.to]
        /\
            LET
                User == msg.to
                FoilPeer == PrevElemIn(User, msg.route)
                StockPeer == NextElemIn(User, msg.route)
            IN
                /\ msg.from = StockPeer
                /\ User # msg.originator
                /\
                    \/ <<User, FoilPeer, Stock>> \in DOMAIN tallies => ProjectedBalance(tallies[<<User, FoilPeer, Stock>>]) - msg.value < 0
                    \/ <<User, StockPeer, Foil>> \in DOMAIN tallies => ProjectedBalance(tallies[<<User, StockPeer, Foil>>]) + msg.value > 0
                /\ lifts' = [lifts EXCEPT ![User] =
                    msg.liftGuid :> [route |-> msg.route, liftType |-> msg.liftType, originator |-> msg.originator,
                        destination |-> msg.destination, value |-> msg.value, expire |-> msg.expire, state |-> Failed] @@ @]
                /\ messages' = messages
                    (-) SetToBag({msg})
                    (+) SetToBag({Message([from |-> User, to |-> StockPeer, type |-> LiftJson, action |-> Fail, liftGuid |-> msg.liftGuid])})
    /\ UNCHANGED <<tallies, paymentsRemaining, linearLiftsRemaining, nextGuid, now>>
    /\ _stateNum' = Print("FailExceedingLiftProposal", _stateNum + 1)

FailLiftWithAlteredTerminus ==
    /\ \E msg \in BagToSet(messages):
        /\ msg.rcvTimer <= 0
        /\ msg.type = LiftJson
        /\ msg.action = Terminus
        /\
            LET
                User == msg.to
                Lift == lifts[User][msg.liftGuid]
                FoilPeer == PrevElemIn(User, Lift.route)
                StockPeer == NextElemIn(User, Lift.route)
            IN
                /\ msg.from = StockPeer
                /\ msg.from = Lift.destination
                /\ User = Lift.originator
                /\ Lift.state = Seek
                /\
                    \/ msg.route # Lift.route
                    \/ msg.liftType # Lift.liftType
                    \/ msg.originator # Lift.originator
                    \/ msg.destination # Lift.destination
                    \/ msg.value # Lift.value
                    \/ msg.expire # Lift.expire
                /\ lifts' = [lifts EXCEPT ![User] = [@ EXCEPT ![msg.liftGuid] = [@ EXCEPT !.state = Failed]]]
                /\ tallies' =
                    [id \in DOMAIN tallies |->
                        CASE id = <<User, FoilPeer, Stock>> -> UpdateLiftChit(tallies[id], msg.liftGuid, Failed)
                        [] id = <<User, StockPeer, Foil>> -> UpdateLiftChit(tallies[id], msg.liftGuid, Failed)
                        [] OTHER -> tallies[id]]
                /\ messages' = messages
                    (-) SetToBag({msg})
                    (+) SetToBag({Message([from |-> User, to |-> StockPeer, type |-> LiftJson, action |-> Fail, liftGuid |-> msg.liftGuid])})
    /\ UNCHANGED <<paymentsRemaining, linearLiftsRemaining, nextGuid, now>>
    /\ _stateNum' = Print("FailLiftWithAlteredTerminus", _stateNum + 1)

HandleLiftFail ==
    /\ \E msg \in BagToSet(messages):
        /\ msg.rcvTimer <= 0
        /\ msg.type = LiftJson
        /\ msg.action = Fail
        /\
            LET
                User == msg.to
                Lift == lifts[User][msg.liftGuid]
                FoilPeer == PrevElemIn(User, Lift.route)
                StockPeer == NextElemIn(User, Lift.route)
            IN
                /\ msg.from = FoilPeer
                /\ Lift.state = IF User = Lift.originator THEN Seek ELSE Pend
                /\ lifts' = [lifts EXCEPT ![User] = [@ EXCEPT ![msg.liftGuid] = [@ EXCEPT !.state = Failed]]]
                /\ tallies' =
                    [id \in DOMAIN tallies |->
                        CASE id = <<User, FoilPeer, Stock>> -> UpdateLiftChit(tallies[id], msg.liftGuid, Failed)
                        [] id = <<User, StockPeer, Foil>> -> UpdateLiftChit(tallies[id], msg.liftGuid, Failed)
                        [] OTHER -> tallies[id]]
                /\ messages' =
                    IF User = Lift.originator THEN
                        messages (-) SetToBag({msg})
                    ELSE
                        messages
                            (-) SetToBag({msg})
                            (+) SetToBag({Message([from |-> User, to |-> StockPeer, type |-> LiftJson, action |-> Fail, liftGuid |-> msg.liftGuid])})
    /\ UNCHANGED <<paymentsRemaining, linearLiftsRemaining, nextGuid, now>>
    /\ _stateNum' = Print("HandleLiftFail", _stateNum + 1)

HandleLiftFailLoopback ==
    /\ \E msg \in BagToSet(messages):
        /\ msg.rcvTimer <= 0
        /\ msg.type = LiftJson
        /\ msg.action = Fail
        /\
            LET
                User == msg.to
                Lift == lifts[User][msg.liftGuid]
                FoilPeer == PrevElemIn(User, Lift.route)
            IN
                /\ msg.from = FoilPeer
                /\ User = Lift.originator
                /\ Lift.state = Failed
                /\ messages' = messages (-) SetToBag({msg})
    /\ UNCHANGED <<tallies, lifts, paymentsRemaining, linearLiftsRemaining, nextGuid, now>>
    /\ _stateNum' = Print("HandleLiftFailLoopback", _stateNum + 1)

IgnoreTimedOutLiftFail ==
    /\ \E msg \in BagToSet(messages):
        /\ msg.rcvTimer <= 0
        /\ msg.type = LiftJson
        /\ msg.action = Fail
        /\
            LET
                User == msg.to
                Lift == lifts[User][msg.liftGuid]
                FoilPeer == PrevElemIn(User, Lift.route)
                StockPeer == NextElemIn(User, Lift.route)
            IN
                /\ msg.from = FoilPeer
                /\ Lift.state = Timeout
                /\ messages' = messages (-) SetToBag({msg})
    /\ UNCHANGED <<tallies, lifts, paymentsRemaining, linearLiftsRemaining, nextGuid, now>>
    /\ _stateNum' = Print("IgnoreTimedOutLiftFail", _stateNum + 1)

(*** Lift Commit (Downstream) ***)

CommitLift ==
    /\ \E msg \in BagToSet(messages):
        /\ msg.rcvTimer <= 0
        /\ msg.type = LiftJson
        /\ msg.action = Terminus
        /\
            LET
                User == msg.to
                Lift == lifts[User][msg.liftGuid]
                FoilPeer == PrevElemIn(User, Lift.route)
                StockPeer == NextElemIn(User, Lift.route)
            IN
                /\ msg.from = StockPeer
                /\ msg.from = Lift.destination
                /\ User = Lift.originator
                /\ Lift.state = Seek
                /\ msg.route = Lift.route
                /\ msg.liftType = Lift.liftType
                /\ msg.originator = Lift.originator
                /\ msg.destination = Lift.destination
                /\ msg.value = Lift.value
                /\ msg.expire = Lift.expire
                /\ lifts' = [lifts EXCEPT ![User] = [@ EXCEPT ![msg.liftGuid] = [@ EXCEPT !.state = Good]]]
                /\ tallies' =
                    [id \in DOMAIN tallies |->
                        CASE id = <<User, FoilPeer, Stock>> -> UpdateLiftChit(tallies[id], msg.liftGuid, Good)
                        [] id = <<User, StockPeer, Foil>> -> UpdateLiftChit(tallies[id], msg.liftGuid, Good)
                        [] OTHER -> tallies[id]]
                /\ messages' = messages
                    (-) SetToBag({msg})
                    (+) SetToBag({Message([from |-> User, to |-> StockPeer, type |-> LiftJson, action |-> Commit, liftGuid |-> msg.liftGuid])})
    /\ UNCHANGED <<paymentsRemaining, linearLiftsRemaining, nextGuid, now>>
    /\ _stateNum' = Print("CommitLift", _stateNum + 1)

HandleLiftCommit ==
    /\ \E msg \in BagToSet(messages):
        /\ msg.rcvTimer <= 0
        /\ msg.type = LiftJson
        /\ msg.action = Commit
        /\
            LET
                User == msg.to
                Lift == lifts[User][msg.liftGuid]
                FoilPeer == PrevElemIn(User, Lift.route)
                StockPeer == NextElemIn(User, Lift.route)
            IN
                /\ msg.from = FoilPeer
                /\ User # Lift.originator
                /\ Lift.state = Pend
                /\ lifts' = [lifts EXCEPT ![User] = [@ EXCEPT ![msg.liftGuid] = [@ EXCEPT !.state = Good]]]
                /\ tallies' =
                    [id \in DOMAIN tallies |->
                        CASE id = <<User, FoilPeer, Stock>> -> UpdateLiftChit(tallies[id], msg.liftGuid, Good)
                        [] id = <<User, StockPeer, Foil>> -> UpdateLiftChit(tallies[id], msg.liftGuid, Good)
                        [] OTHER -> tallies[id]]
                /\ messages' = messages
                    (-) SetToBag({msg})
                    (+) SetToBag({Message([from |-> User, to |-> StockPeer, type |-> LiftJson, action |-> Commit, liftGuid |-> msg.liftGuid])})
    /\ UNCHANGED <<paymentsRemaining, linearLiftsRemaining, nextGuid, now>>
    /\ _stateNum' = Print("HandleLiftCommit", _stateNum + 1)

HandleLiftCommitLoopback ==
    /\ \E msg \in BagToSet(messages):
        /\ msg.rcvTimer <= 0
        /\ msg.type = LiftJson
        /\ msg.action = Commit
        /\
            LET
                User == msg.to
                Lift == lifts[User][msg.liftGuid]
                FoilPeer == PrevElemIn(User, Lift.route)
            IN
                /\ msg.from = FoilPeer
                /\ User = Lift.originator
                /\ Lift.state = Good
                /\ messages' = messages (-) SetToBag({msg})
    /\ UNCHANGED <<tallies, lifts, paymentsRemaining, linearLiftsRemaining, nextGuid, now>>
    /\ _stateNum' = Print("HandleLiftCommitLoopback", _stateNum + 1)

(*** Time Control ***)

Tick ==
    /\ now < TimeLimit \* Make state space finite
    /\ \A msg \in BagToSet(messages): msg.rcvTimer - 1 >= 0
    /\ \A id \in DOMAIN StockTallies: \A i \in DOMAIN tallies[id].chits:
        LET Chit == tallies[id].chits[i]
        IN (Chit.type = PaymentType /\ Chit.state = Invoiced) => now + 1 <= Chit.expire
    /\ \A user \in Users: \A guid \in DOMAIN lifts[user]:
        LET Lift == lifts[user][guid]
        IN Lift.state = Seek => now + 1 <= Lift.expire
    /\ now' = now + 1
    /\ messages' =
        LET UpdateTimer(msg) == [msg EXCEPT !.rcvTimer = @ - 1]
        IN BagOfAll(UpdateTimer, messages)
    /\ UNCHANGED <<tallies, lifts, paymentsRemaining, linearLiftsRemaining, nextGuid>>
    /\ _stateNum' = Print("Tick", _stateNum + 1)

(*** ***)

Next ==
    \/ SendPayment
    \/ ReceivePayment
    \/ SendInvoice
    \/ PayInvoice
    \/ DeclineInvoice
    \/ ReceivePaidInvoice
    \/ ReceiveDeclinedInvoice
    \/ TimeOutInvoice
    \/ ProposeCircularLift
    \/ ProposeLinearLift
    \/ HandleLiftProposal
    \/ MaliciouslyHandleLiftProposal
    \/ IgnoreTimedOutLiftProposal
    \/ IgnoreTimedOutLiftTerminus
    \/ TimeOutLift
    \/ HandleLiftTimeout
    \/ HandleUnknownLiftTimeout
    \/ HandleLiftTimeoutLoopback
    \/ IgnoreFailedLiftTimeout
    \/ FailExceedingLiftProposal
    \/ FailLiftWithAlteredTerminus
    \/ HandleLiftFail
    \/ HandleLiftFailLoopback
    \/ IgnoreTimedOutLiftFail
    \/ CommitLift
    \/ HandleLiftCommit
    \/ HandleLiftCommitLoopback
    \/ Tick

Fairness ==
    /\ SF_vars(SendPayment)
    /\ WF_vars(ReceivePayment)
    /\ SF_vars(SendInvoice)
    /\ SF_vars(PayInvoice)
    /\ SF_vars(DeclineInvoice)
    /\ WF_vars(ReceivePaidInvoice)
    /\ WF_vars(ReceiveDeclinedInvoice)
    /\ SF_vars(TimeOutInvoice)
    /\ SF_vars(ProposeCircularLift)
    /\ SF_vars(ProposeLinearLift)
    /\ SF_vars(HandleLiftProposal)
    /\ SF_vars(MaliciouslyHandleLiftProposal)
    /\ WF_vars(IgnoreTimedOutLiftProposal)
    /\ WF_vars(IgnoreTimedOutLiftTerminus)
    /\ SF_vars(TimeOutLift)
    /\ SF_vars(HandleLiftTimeout)
    /\ SF_vars(HandleUnknownLiftTimeout)
    /\ WF_vars(HandleLiftTimeoutLoopback)
    /\ WF_vars(IgnoreFailedLiftTimeout)
    /\ SF_vars(FailExceedingLiftProposal)
    /\ SF_vars(FailLiftWithAlteredTerminus)
    /\ SF_vars(HandleLiftFail)
    /\ WF_vars(HandleLiftFailLoopback)
    /\ WF_vars(IgnoreTimedOutLiftFail)
    /\ SF_vars(CommitLift)
    /\ WF_vars(HandleLiftCommit)
    /\ WF_vars(HandleLiftCommitLoopback)
    /\ WF_vars(Tick)

Spec == Init /\ [][Next]_vars /\ Fairness

NoConversationBetween(x, y) == ~\E msg \in BagToSet(messages): {msg.from, msg.to} = {x, y}

UserLiftsInProgress(user) == {guid \in DOMAIN lifts[user]: lifts[user][guid].state \in {Seek, Pend}}

UserLinearLiftsInProgress(user) == {guid \in UserLiftsInProgress(user): lifts[user][guid].liftType = Linear}

NoPaymentsInProgress == ~\E msg \in BagToSet(messages): msg.type = ChitJson

NoLiftsInProgress == \A user \in Users: UserLiftsInProgress(user) = {}

NoLinearLiftsInProgress == \A user \in Users: UserLinearLiftsInProgress(user) = {}

NoInvoicedChits == \A id \in DOMAIN tallies: \A i \in DOMAIN tallies[id].chits: tallies[id].chits[i].state # Invoiced

GetLiftChit(tally, liftGuid) ==
    LET ChitIndexes == {i \in DOMAIN tally.chits: tally.chits[i].type = LiftType /\ tally.chits[i].liftGuid = liftGuid}
    IN CASE Cardinality(ChitIndexes) = 1 -> tally.chits[CHOOSE chit \in ChitIndexes: TRUE]

PartnersBalancesAreSymmetrical ==
    \A <<x, y, type>> \in DOMAIN FoilTallies:
        (
            /\ NoConversationBetween(x, y)
            /\ UserLiftsInProgress(x) = UserLiftsInProgress(y)
        ) => (
            /\ AvailableBalance(tallies[<<x, y, Foil>>]) = -AvailableBalance(tallies[<<y, x, Stock>>])
            /\ ProjectedBalance(tallies[<<x, y, Foil>>]) = -ProjectedBalance(tallies[<<y, x, Stock>>])
        )

ProjectedAndAvailableBalancesAreEqualWhenNoLiftsInProgress ==
    \A <<x, y, type>> \in DOMAIN tallies:
        UserLiftsInProgress(x) = {} =>
            ProjectedBalance(tallies[<<x, y, type>>]) = AvailableBalance(tallies[<<x, y, type>>])

FoilBalancesAreNotPositive ==
    \A id \in DOMAIN FoilTallies:
        /\ AvailableBalance(tallies[id]) <= 0
        /\ ProjectedBalance(tallies[id]) <= 0

StockBalancesAreNotNegative ==
    \A id \in DOMAIN StockTallies:
        /\ AvailableBalance(tallies[id]) >= 0
        /\ ProjectedBalance(tallies[id]) >= 0

UsersChitsOfGoodLiftsAreSymmetrical ==
    \A user \in Users: \A liftGuid \in DOMAIN lifts[user]:
        LET Lift == lifts[user][liftGuid]
        IN
            (
                /\ Lift.state = Good
                /\
                    \/ Lift.liftType = Circular
                    \/
                        /\ Lift.liftType = Linear
                        /\ user # Lift.originator
                        /\ user # Lift.destination
            ) => (
                LET
                    FoilPeer == PrevElemIn(user, Lift.route)
                    StockPeer == NextElemIn(user, Lift.route)
                IN
                    GetLiftChit(tallies[<<user, StockPeer, Foil>>], liftGuid).value = -GetLiftChit(tallies[<<user, FoilPeer, Stock>>], liftGuid).value
            )

AvailableMoneySumIsZero ==
    (
        /\ NoPaymentsInProgress
        /\ NoLinearLiftsInProgress
    ) =>
        Sum([id \in DOMAIN tallies |-> AvailableBalance(tallies[id])]) = 0

ProjectedMoneySumIsZero ==
    (
        /\ NoPaymentsInProgress
        /\ NoLiftsInProgress
    ) =>
        Sum([id \in DOMAIN tallies |-> ProjectedBalance(tallies[id])]) = 0

Terminal ==
    /\ paymentsRemaining = 0
    /\ messages = EmptyBag
    /\ NoInvoicedChits
    /\ NoLiftsInProgress
    /\ \A cycle \in Cycles: MaxLiftValueFor(cycle, AvailableBalance) = 0
    /\
        \/ linearLiftsRemaining = 0
        \/ \A polyline \in Polylines: MaxLiftValueFor(polyline, AvailableBalance) = 0

Termination == <>[]Terminal

\* Special invariant to get "error" trace for first found interesting state
NotInteresting == ~Terminal

=============================================================================
