\*MyCHIPs payments and lifts specification module.
\*Copyright MyCHIPs.org; See license in root of this package
\* -------------------------------------------------------------------------
\* Specifies voluntary payments, payments of invoices, circular and linear
\* lifts. Assumes that each user is hosted at its individual site. Includes
\* an example of malicious behavior when at the lift proposal phase
\* a non-originator user reduces (in magnitude) the value in the pending
\* chit being added to their stock tally and sends the query/terminus
\* message with this reduced value to the foil peer.

------------------------------- MODULE RefereeLifts -------------------------------

EXTENDS Integers, Sequences, FiniteSets, Bags, TLC

CONSTANTS
    Users,
    Links,
    Cycles,
    Polylines,
    NewStateLimit,
    PaymentsRange,
    PaymentsCount,
    LinearLiftsCount,
    GLOBAL_REF

ASSUME
    /\ Links \subseteq Users \X Users \* Links are a pair of users (user, user)
    /\ \A link \in Links: link[1] # link[2] \* Links don't connect to self (userA, userB) A != B

NextIndexIn(i, ring) == (i % Len(ring)) + 1  \* 1 indexed between 1 and length

PrevIndexIn(i, ring) == ((i - 2) % Len(ring)) + 1 \* -2 +1 to get correctly in 1 ... len
\* not sure why this is not 0 indexed. I assume personal preferences

ASSUME \A cycle \in Cycles: \* for all cycles
    /\ \A i \in 1..Len(cycle): cycle[i] \in Users \* cycles are containers of only users
    /\ \A i, j \in 1..Len(cycle): i # j => cycle[i] # cycle[j] \* no user appears twice in the cycle (this may be invalid)
    /\ \A i \in 1..Len(cycle): <<cycle[i], cycle[NextIndexIn(i, cycle)]>> \in Links \* every item in the cycle is linked with the next item
    \* need to ensure Links is symmetric

ASSUME \A polyline \in Polylines:
    /\ \A i \in 1..Len(polyline): polyline[i] \in Users \* polylines are containers of only users
    /\ \A i, j \in 1..Len(polyline): i # j => polyline[i] # polyline[j] \* no user appears twice in a polyline (this may be invalid)
    /\ \A i \in 1..(Len(polyline) - 1): <<polyline[i], polyline[i + 1]>> \in Links \* evry item in line is connected with next
    /\ <<polyline[Len(polyline)], polyline[1]>> \notin Links \* The end of the line is not linked with the begining

ASSUME PaymentsRange \in {range \in SUBSET Nat: \E min, max \in 1..999: min <= max /\ range = min..max}
\* PaymentsRange is a range of numbers with min at least 1 and max at most 999.

ASSUME PaymentsCount \in Int \*Payments Count is some integer (could be negative... why?)

ASSUME
    /\ LinearLiftsCount \in Int \* Linear Lifts Count is some integer
    /\ LinearLiftsCount >= 0 \* that cannot be negative


VARIABLES \* These are things that can change during the analysis
    tallies,
    lifts,
    messages,
    paymentsRemaining,
    linearLiftsRemaining,
    nextGuid,
    _stateNum

\*vars is a list of all the variables in the analysis
vars == <<tallies, lifts, messages, paymentsRemaining, linearLiftsRemaining, nextGuid, _stateNum>>

\*define constants to check types for various objects
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

\* Lift Referee Responses
Validate == "Validate"
\* Timeout == "Timeout" - allready defined in Chit states section

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

NextElemIn(elem, ring) == \*syntactic sugar to get next element in cycle using User not index
    LET I == CHOOSE i \in 1..Len(ring): ring[i] = elem
    IN ring[NextIndexIn(I, ring)]

PrevElemIn(elem, ring) == \*syntactic sugar to get previous element in cycle using User not index
    LET I == CHOOSE i \in 1..Len(ring): ring[i] = elem
    IN ring[PrevIndexIn(I, ring)]

RECURSIVE Sum(_)
Sum(f) ==
    IF DOMAIN f = {} THEN \* if there are no items left in the domain of the query
        0 \*the sum is 0
    ELSE \*otherwise
        LET X == CHOOSE x \in DOMAIN f: TRUE \* X is a function that returns an index to an arbitrary item in f
        IN f[X] + Sum([y \in DOMAIN f \ {X} |-> f[y]]) \* Add the arbitrary item to the Sum of f excluding X
        \* y is a domain that has all of f except X. y is a set. f[y] is the set of all items excluding X.
\* Summary. Recursivly selects an item in f and adds it to the sum of f excluding that item


\* 3 is a magic number here. I believe it has to do with the data structure of tallies
TalliesOfType(type) == [id \in {id \in DOMAIN tallies: id[3] = type} |-> tallies[id]] \* gets all tallies of a given type

FoilTallies == TalliesOfType(Foil) \* convinence to get all foils
StockTallies == TalliesOfType(Stock) \* convinence to get all Stocks

ProjectedBalance(tally) ==
    LET ValidChitIndexes == {i \in DOMAIN tally.chits: tally.chits[i].state \in {Good, Pend}} \* get all chits in tally that are good or pending
    IN Sum([i \in ValidChitIndexes |-> tally.chits[i].value]) \* sum their total value (chit values can be positve or negative?)

FoilsProjectedBalances == [id \in DOMAIN FoilTallies |-> ProjectedBalance(tallies[id])] \* sums projected balance of all foils in system
StocksProjectedBalances == [id \in DOMAIN StockTallies |-> ProjectedBalance(tallies[id])] \* sums projected balance of all stocks in system 

AvailableBalance(tally) ==
    LET GoodChitIndexes == {i \in DOMAIN tally.chits: tally.chits[i].state = Good} \* get all chits in tally that are good
    IN Sum([i \in GoodChitIndexes |-> tally.chits[i].value]) \* sum the total value

FoilAvailableBalances == [id \in DOMAIN FoilTallies |-> AvailableBalance(tallies[id])] \* sums available balance of all foils in system
StocksAvailableBalances == [id \in DOMAIN StockTallies |-> AvailableBalance(tallies[id])] \* sums available balance of all stocks in system

AddChit(tally, chit) == [tally EXCEPT !.chits = Append(@, chit)] \* returns an objectf equal to tally except that tally.chits = Append(tally.chits, chit)
\*Append is a tla language function that appends an item to a list

UpdateChit(tally, chitType, guidFieldName, guid, state) == \* updates the state of a chit with the given properties
    [tally EXCEPT !.chits =
        [i \in DOMAIN tally.chits |-> \* for all chits in the given tally
            [tally.chits[i] EXCEPT !.state = \* return a chit equal to the chit in the tally except that the state is changed to
                IF
                    /\ tally.chits[i].type = chitType \* if the type matches the search
                    /\ tally.chits[i][guidFieldName] = guid \* and the arbitrary property (guidFieldName) matches the seearch
                THEN
                    state \* set the state to the provided state
                ELSE
                    tally.chits[i].state]]] \* set the state to the existing state (don't make a change)

UpdateLiftChit(tally, liftGuid, state) == UpdateChit(tally, LiftType, "liftGuid", liftGuid, state) \* syntactic sugar

UpdatePaymentChit(tally, paymentGuid, state) == UpdateChit(tally, PaymentType, "paymentGuid", paymentGuid, state) \* syntactic sugar

\* Message(msg) == msg @@ "rcvTimer" :> RandomElement(TransmitTime[{msg.from, msg.to}]) 
\* Take the msg you give me and add a new mapping that maps "recTimer" to a random amount of time
 
Values(f) == {f[x]: x \in DOMAIN f} \* the set defined by f[x] where x is in the domain of f (to convert a list to set?)

Min(s) == CHOOSE x \in s: \A y \in s: y >= x \* returns an arbitrary min value (there could be more then one)

Max(s) == CHOOSE x \in s: \A y \in s: y <= x \* returns an arbitrary max value (there could be more then one)

\* gets the minimum stock or foil balance along the route (assumes no one will want to have a postive foil or negative stock)
MaxLiftValueFor(route, balance(_)) == Min( \* takes a route (cycle?) and a function named balance that takes one argument
    Values([stockId \in {id \in DOMAIN tallies: \* get the set of balances for all stocks in the route
        \* the set of stockIds where a stockId is some id in tallies
        \E i \in DOMAIN route: <<route[i], route[PrevIndexIn(i, route)], Stock>> = id} 
        \* where we connect backwards in the route and it is of "Stock" type
            |-> balance(tallies[stockId])]) \union \* call balance on each of those stock ids and make the set
    \* union the set of stock balances with the set of foil balances
    Values([foilId \in {id \in DOMAIN tallies: \* get the set of all balances for all the foils in the route
        \E i \in DOMAIN route: <<route[i], route[NextIndexIn(i, route)], Foil>> = id}
            |-> -balance(tallies[foilId])])) \* negate the foil balances to get a positive number

(*** Initial State ***)

Init ==
    /\ tallies = [id \in UNION {{<<x, y, Foil>>, <<y, x, Stock>>}: <<x, y>> \in Links} |-> [chits |-> <<>>]]
    \* tallies is a map that maps tuples <<x, y, Foil>> or <<y, x, Stock>> where x is linked to y to a record that maps chits to empty tuples
    \* eg tallies[a, b, Foil] maps to an empty list if a links with b. (Creates an empty holding place to hold chits, i.e a tally)
    /\ lifts = [user \in Users |-> [liftGuid \in {} |-> 0]]
    \* maps all users to an item in the empty set (what does that mean?) which (a big empty map?) TODO understand this better
    /\ messages = EmptyBag \* a bag is a set that can contain duplicates
    /\ paymentsRemaining = PaymentsCount \* paymentsRemaining is initalized to Payments Count
    /\ linearLiftsRemaining = LinearLiftsCount \* ^...
    /\ nextGuid = 101 \* unique identifier implemented as a count (start at 101 to avoiod collisions?)
    /\ _stateNum = 1 \* count to get unique state ids 
    /\ Print("Init", _stateNum) = 1 \*print statements return 1 when successful for status

(*** Voluntary Payment ***)

SendPayment == \* returns true if
    /\ paymentsRemaining > 0 \* payments remaining is positive
    /\ \E <<foil, stock, type>> \in DOMAIN FoilTallies: \* if there exists a tally such that
        /\ tallies' = [tallies EXCEPT ![<<foil, stock, Foil>>] = \* side effecting add new chit that is allready good
            AddChit(@, [value |-> -RandomElement(PaymentsRange), type |-> PaymentType, paymentGuid |-> nextGuid, state |-> Good])] \* pay a random amount
        /\
            LET
                Chits == tallies'[<<foil, stock, Foil>>].chits
                NewChit == Chits[Len(Chits)]
            IN
                messages' = messages \* put the message in the "messages" bag that would have fulfilled this event
                    (+) SetToBag({(
                        [from |-> foil, to |-> stock, type |-> ChitJson, action |-> PeerValid, paymentGuid |-> nextGuid, value |-> -NewChit.value])})
        /\ nextGuid' = nextGuid + 1 \* make sure nextGuid will be unique
        /\ paymentsRemaining' = paymentsRemaining - 1 \* subtract 1 from payments remaining
    /\ UNCHANGED <<lifts, linearLiftsRemaining>> \* was not a lift, and took no time
    /\ _stateNum' = Print("SendPayment", _stateNum + 1) \* print for progress

ReceivePayment ==
    /\ \E msg \in BagToSet(messages): \* if there is a message in the bag
        /\ msg.type = ChitJson \* and it has a chit
        /\ msg.action = PeerValid \* (this was set in send payment not sure what PeerValid is supposed to represent)
        /\
            LET Tally == tallies[<<msg.to, msg.from, Stock>>]
            IN
                ~\E i \in DOMAIN Tally.chits:
                    /\ Tally.chits[i].type = PaymentType
                    /\ Tally.chits[i].paymentGuid = msg.paymentGuid
        /\ tallies' = [tallies EXCEPT ![<<msg.to, msg.from, Stock>>] =
            AddChit(@, [value |-> msg.value, type |-> PaymentType, paymentGuid |-> msg.paymentGuid, state |-> Good])]
        /\ messages' = messages (-) SetToBag({msg})
    /\ UNCHANGED <<lifts, paymentsRemaining, linearLiftsRemaining, nextGuid>>
    /\ _stateNum' = Print("ReceivePayment", _stateNum + 1)

(*** Payment of Invoice ***)

SendInvoice ==
    /\ paymentsRemaining > 0
    /\ \E <<stock, foil, type>> \in DOMAIN StockTallies:
        /\ tallies' = [tallies EXCEPT ![<<stock, foil, Stock>>] =
            AddChit(@, [value |-> RandomElement(PaymentsRange), type |-> PaymentType, paymentGuid |-> nextGuid, state |-> Invoiced])]
        /\
            LET
                Chits == tallies'[<<stock, foil, Stock>>].chits
                NewChit == Chits[Len(Chits)]
            IN
                messages' = messages
                    (+) SetToBag({(
                        [from |-> stock, to |-> foil, type |-> ChitJson, action |-> PeerInvoice,
                        paymentGuid |-> nextGuid, value |-> NewChit.value])})
        /\ nextGuid' = nextGuid + 1
        /\ paymentsRemaining' = paymentsRemaining - 1
    /\ UNCHANGED <<lifts, linearLiftsRemaining>>
    /\ _stateNum' = Print("SendInvoice", _stateNum + 1)

PayInvoice ==
    /\ \E msg \in BagToSet(messages):
        /\ msg.type = ChitJson
        /\ msg.action = PeerInvoice
        /\
            LET Tally == tallies[<<msg.to, msg.from, Foil>>]
            IN
                ~\E i \in DOMAIN Tally.chits:
                    /\ Tally.chits[i].type = PaymentType
                    /\ Tally.chits[i].paymentGuid = msg.paymentGuid
        /\ tallies' = [tallies EXCEPT ![<<msg.to, msg.from, Foil>>] =
            AddChit(@, [value |-> -msg.value, type |-> PaymentType, paymentGuid |-> msg.paymentGuid, state |-> Good])]
        /\ messages' = messages
            (-) SetToBag({msg})
            (+) SetToBag({(
                [from |-> msg.to, to |-> msg.from, type |-> ChitJson, action |-> PeerValid,
                paymentGuid |-> msg.paymentGuid, value |-> msg.value])})
    /\ UNCHANGED <<lifts, paymentsRemaining, linearLiftsRemaining, nextGuid>>
    /\ _stateNum' = Print("PayInvoice", _stateNum + 1)

DeclineInvoice ==
    /\ \E msg \in BagToSet(messages):
        /\ msg.type = ChitJson
        /\ msg.action = PeerInvoice
        /\
            LET Tally == tallies[<<msg.to, msg.from, Foil>>]
            IN
                ~\E i \in DOMAIN Tally.chits:
                    /\ Tally.chits[i].type = PaymentType
                    /\ Tally.chits[i].paymentGuid = msg.paymentGuid
        /\ tallies' = [tallies EXCEPT ![<<msg.to, msg.from, Foil>>] =
            AddChit(@, [value |-> -msg.value, type |-> PaymentType, paymentGuid |-> msg.paymentGuid, state |-> Failed])]
        /\ messages' = messages
            (-) SetToBag({msg})
            (+) SetToBag({(
                [from |-> msg.to, to |-> msg.from, type |-> ChitJson, action |-> PeerDecline,
                paymentGuid |-> msg.paymentGuid, value |-> msg.value])})
    /\ UNCHANGED <<lifts, paymentsRemaining, linearLiftsRemaining, nextGuid>>
    /\ _stateNum' = Print("DeclineInvoice", _stateNum + 1)

ReceivePaidInvoice ==
    /\ \E msg \in BagToSet(messages):
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
        /\ tallies' = [tallies EXCEPT ![<<msg.to, msg.from, Stock>>] = UpdatePaymentChit(@, msg.paymentGuid, Good)]
        /\ messages' = messages (-) SetToBag({msg})
    /\ UNCHANGED <<lifts, paymentsRemaining, linearLiftsRemaining, nextGuid>>
    /\ _stateNum' = Print("ReceivePaidInvoice", _stateNum + 1)

ReceiveDeclinedInvoice ==
    /\ \E msg \in BagToSet(messages):
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
        /\ tallies' = [tallies EXCEPT ![<<msg.to, msg.from, Stock>>] = UpdatePaymentChit(@, msg.paymentGuid, Failed)]
        /\ messages' = messages (-) SetToBag({msg})
    /\ UNCHANGED <<lifts, paymentsRemaining, linearLiftsRemaining, nextGuid>>
    /\ _stateNum' = Print("ReceiveDeclinedInvoice", _stateNum + 1)

(*
TimeOutInvoice == \* TODO FLESH OUT THIS ACTION TO IGNORE CONCEPT OF TIME (AND TO REFERENCE REFEREE)
    \E id \in DOMAIN StockTallies: \E i \in DOMAIN tallies[id].chits:
        LET Chit == tallies[id].chits[i]
        IN
            /\ Chit.type = PaymentType
            /\ Chit.state = Invoiced
        /\ tallies' = [tallies EXCEPT ![id] = UpdatePaymentChit(@, tallies[id].chits[i].paymentGuid, Timeout)]
    /\ UNCHANGED <<lifts, messages, paymentsRemaining, linearLiftsRemaining, nextGuid>>
    /\ _stateNum' = Print("TimeOutInvoice", _stateNum + 1)

*)

(*** Lift Proposal (Upstream) ***)

ProposeLift(route, liftType, value, referee) ==
    /\
        LET
            User == route[Len(route)]
            FoilPeer == PrevElemIn(User, route)
            StockPeer == NextElemIn(User, route)
        IN
            /\ lifts' = [lifts EXCEPT ![User] =
                nextGuid :> [route |-> route, liftType |-> liftType, originator |-> User, destination |-> StockPeer,
                    value |-> value, referee |-> referee, state |-> Seek] @@ @]
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
                        (+) SetToBag({(
                            [from |-> User, to |-> FoilPeer, type |-> LiftJson, action |-> Query, liftGuid |-> nextGuid,
                            route |-> NewLift.route, liftType |-> NewLift.liftType, originator |-> NewLift.originator,
                            destination |-> NewLift.destination, value |-> NewLift.value, referee |-> NewLift.referee])})
            /\ nextGuid' = nextGuid + 1
    /\ UNCHANGED <<paymentsRemaining>>

ProposeCircularLift ==
    /\ \E cycle \in Cycles:
        LET MaxLiftValue == MaxLiftValueFor(cycle, ProjectedBalance)
        IN
            /\ MaxLiftValue > 0
            /\ \E i \in DOMAIN cycle:
                LET Route == [j \in DOMAIN cycle |-> cycle[((j - 1 + i) % Len(cycle)) + 1]]
                IN ProposeLift(Route, Circular, RandomElement(1..MaxLiftValue), GLOBAL_REF)
    /\ UNCHANGED <<linearLiftsRemaining>>
    /\ _stateNum' = Print("ProposeCircularLift", _stateNum + 1)

ProposeLinearLift ==
    /\ linearLiftsRemaining > 0
    /\ \E route \in Polylines:
        LET MaxLiftValue == MaxLiftValueFor(route, ProjectedBalance)
        IN
            /\ MaxLiftValue > 0
            /\ ProposeLift(route, Linear, RandomElement(1..MaxLiftValue), GLOBAL_REF)
            /\ linearLiftsRemaining' = linearLiftsRemaining - 1
    /\ _stateNum' = Print("ProposeLinearLift", _stateNum + 1)

HandleLiftProposal ==
    /\ \E msg \in BagToSet(messages):
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
                        destination |-> msg.destination, value |-> msg.value, referee |-> msg.referee, state |-> Pend] @@ @]
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
                    (+) SetToBag({(
                        [from |-> User, to |-> FoilPeer, type |-> LiftJson, action |-> IF User = msg.destination THEN Terminus ELSE Query,
                        liftGuid |-> msg.liftGuid, route |-> msg.route, liftType |-> msg.liftType, originator |-> msg.originator,
                        destination |-> msg.destination, value |-> msg.value, referee |-> msg.referee])})
    /\ UNCHANGED <<paymentsRemaining, linearLiftsRemaining, nextGuid>>
    /\ _stateNum' = Print("HandleLiftProposal", _stateNum + 1)



IgnoreTimedOutLiftProposal ==
    /\ \E msg \in BagToSet(messages):
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
    /\ UNCHANGED <<tallies, lifts, paymentsRemaining, linearLiftsRemaining, nextGuid>>
    /\ _stateNum' = Print("IgnoreTimedOutLiftProposal", _stateNum + 1)

IgnoreTimedOutLiftTerminus ==
    /\ \E msg \in BagToSet(messages):
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
    /\ UNCHANGED <<tallies, lifts, paymentsRemaining, linearLiftsRemaining, nextGuid>>
    /\ _stateNum' = Print("IgnoreTimedOutLiftTerminus", _stateNum + 1)

(*** Lift Timeout (Upstream) ***)

(* This will be used to have nodes occasionally request from the Referee if the lift has timed out
AskTimeOutLift == \* TODO Flesh this out with Referee stuff
    \E user \in Users: \E liftGuid \in DOMAIN lifts[user]:
        LET Lift == lifts[user][liftGuid]
        IN
            /\ Lift.state = Seek
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
                        (+) SetToBag({(
                            [from |-> user, to |-> FoilPeer, type |-> LiftJson, action |-> Timeout, liftGuid |-> liftGuid,
                            route |-> Lift.route, liftType |-> Lift.liftType, originator |-> Lift.originator,
                            destination |-> Lift.destination, value |-> Lift.value])})
    /\ UNCHANGED <<paymentsRemaining, linearLiftsRemaining, nextGuid>>
    /\ _stateNum' = Print("TimeOutLift", _stateNum + 1)
    
*)

HandleLiftTimeout ==
    /\ \E msg \in BagToSet(messages):
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
                    (+) SetToBag({(
                        [from |-> User, to |-> FoilPeer, type |-> LiftJson, action |-> Timeout, liftGuid |-> msg.liftGuid,
                        route |-> msg.route, liftType |-> msg.liftType, originator |-> msg.originator,
                        destination |-> msg.destination, value |-> msg.value, referee |-> msg.referee])})
    /\ UNCHANGED <<paymentsRemaining, linearLiftsRemaining, nextGuid>>
    /\ _stateNum' = Print("HandleLiftTimeout", _stateNum + 1)

HandleUnknownLiftTimeout ==
    /\ \E msg \in BagToSet(messages):
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
                        destination |-> msg.destination, value |-> msg.value, referee |-> msg.referee, state |-> Timeout] @@ @]
                /\ messages' = messages
                    (-) SetToBag({msg})
                    (+) SetToBag({(
                        [from |-> User, to |-> FoilPeer, type |-> LiftJson, action |-> Timeout, liftGuid |-> msg.liftGuid,
                        route |-> msg.route, liftType |-> msg.liftType, originator |-> msg.originator,
                        destination |-> msg.destination, value |-> msg.value, referee |-> msg.referee])})
    /\ UNCHANGED <<tallies, paymentsRemaining, linearLiftsRemaining, nextGuid>>
    /\ _stateNum' = Print("HandleUnknownLiftTimeout", _stateNum + 1)

HandleLiftTimeoutLoopback ==
    /\ \E msg \in BagToSet(messages):
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
    /\ UNCHANGED <<tallies, lifts, paymentsRemaining, linearLiftsRemaining, nextGuid>>
    /\ _stateNum' = Print("HandleLiftTimeoutLoopback", _stateNum + 1)

IgnoreFailedLiftTimeout ==
    /\ \E msg \in BagToSet(messages):
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
    /\ UNCHANGED <<tallies, lifts, paymentsRemaining, linearLiftsRemaining, nextGuid>>
    /\ _stateNum' = Print("IgnoreFailedLiftTimeout", _stateNum + 1)

(*** Lift Fail (Downstream) ***)

FailExceedingLiftProposal ==
    /\ \E msg \in BagToSet(messages):
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
                        destination |-> msg.destination, value |-> msg.value, referee |-> msg.referee, state |-> Failed] @@ @]
                /\ messages' = messages
                    (-) SetToBag({msg})
                    (+) SetToBag({([from |-> User, to |-> StockPeer, type |-> LiftJson, action |-> Fail, liftGuid |-> msg.liftGuid])})
    /\ UNCHANGED <<tallies, paymentsRemaining, linearLiftsRemaining, nextGuid>>
    /\ _stateNum' = Print("FailExceedingLiftProposal", _stateNum + 1)

FailLiftWithAlteredTerminus ==
    /\ \E msg \in BagToSet(messages):
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
                /\ lifts' = [lifts EXCEPT ![User] = [@ EXCEPT ![msg.liftGuid] = [@ EXCEPT !.state = Failed]]]
                /\ tallies' =
                    [id \in DOMAIN tallies |->
                        CASE id = <<User, FoilPeer, Stock>> -> UpdateLiftChit(tallies[id], msg.liftGuid, Failed)
                        [] id = <<User, StockPeer, Foil>> -> UpdateLiftChit(tallies[id], msg.liftGuid, Failed)
                        [] OTHER -> tallies[id]]
                /\ messages' = messages
                    (-) SetToBag({msg})
                    (+) SetToBag({([from |-> User, to |-> StockPeer, type |-> LiftJson, action |-> Fail, liftGuid |-> msg.liftGuid])})
    /\ UNCHANGED <<paymentsRemaining, linearLiftsRemaining, nextGuid>>
    /\ _stateNum' = Print("FailLiftWithAlteredTerminus", _stateNum + 1)

HandleLiftFail ==
    /\ \E msg \in BagToSet(messages):
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
                            (+) SetToBag({([from |-> User, to |-> StockPeer, type |-> LiftJson, action |-> Fail, liftGuid |-> msg.liftGuid])})
    /\ UNCHANGED <<paymentsRemaining, linearLiftsRemaining, nextGuid>>
    /\ _stateNum' = Print("HandleLiftFail", _stateNum + 1)

HandleLiftFailLoopback ==
    /\ \E msg \in BagToSet(messages):
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
    /\ UNCHANGED <<tallies, lifts, paymentsRemaining, linearLiftsRemaining, nextGuid>>
    /\ _stateNum' = Print("HandleLiftFailLoopback", _stateNum + 1)

IgnoreTimedOutLiftFail ==
    /\ \E msg \in BagToSet(messages):
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
    /\ UNCHANGED <<tallies, lifts, paymentsRemaining, linearLiftsRemaining, nextGuid>>
    /\ _stateNum' = Print("IgnoreTimedOutLiftFail", _stateNum + 1)

(*** Lift Commit (Downstream) ***)
RequestLiftValidation ==
    /\ \E msg \in BagToSet(messages):
        /\ msg.type = LiftJson
        /\ msg.action = Terminus
        /\
            LET
                User == msg.to
                Lift == lifts[User][msg.liftGuid]
                Referee == msg.referee
                StockPeer == NextElemIn(User, Lift.route)
            IN
                /\ msg.from = StockPeer \* make sure everything matches and is in order
                /\ msg.from = Lift.destination
                /\ User = Lift.originator
                /\ Lift.state = Seek
                /\ msg.route = Lift.route
                /\ msg.liftType = Lift.liftType
                /\ msg.originator = Lift.originator
                /\ msg.destination = Lift.destination
                /\ msg.value = Lift.value
                
                /\ messages' = messages \* send a message to the REF to get them to verify time
                    (-) SetToBag({msg})
                    (+) SetToBag({(
                        [from |-> User, to |-> Referee, type |-> LiftJson, action |-> Validate, liftGuid |-> msg.liftGuid,
                        route |-> msg.route, liftType |-> msg.liftType, originator |-> msg.originator,
                        destination |-> msg.destination, value |-> msg.value, referee |-> Referee])})
    /\ UNCHANGED <<paymentsRemaining, linearLiftsRemaining, nextGuid>>
    /\ _stateNum' = Print("RequestValidation", _stateNum + 1)
                
    
HandleLiftValidation ==
    /\ \E msg \in BagToSet(messages):
        /\ msg.type = LiftJson
        /\ msg.action = Validate
        /\ msg.liftGuid \in DOMAIN lifts[msg.to] \* check the lift is in your records
        /\
            LET 
                User == msg.to
                Lift == lifts[User][msg.liftGuid]
                Referee == msg.referee
                Originator == msg.originator
                Result == Validate \* RandomElement({Timeout, Validate}) TODO sometimes timeout
            IN
                /\ msg.from = Originator
                /\ msg.to = Referee
                /\ lifts' = [lifts EXCEPT ![User] = [@ EXCEPT ![msg.liftGuid] = [@ EXCEPT !.state = Good]]]
                
                /\ messages' = messages
                    (-) SetToBag({msg}) 
                    (+) SetToBag({(
                        [from |-> Referee, to |-> Originator, type |-> LiftJson, action |-> Result, \* randomlly decides if it's timedout or valid
                        liftGuid |-> msg.liftGuid, route |-> msg.route, liftType |-> msg.liftType, originator |-> Originator,
                        destination |-> msg.destination, value |-> msg.value, referee |-> msg.referee])})
    /\ UNCHANGED <<tallies, paymentsRemaining, linearLiftsRemaining, nextGuid>>
    /\ _stateNum' = Print("ValidateLift", _stateNum + 1)          

CommitLift ==
    /\ \E msg \in BagToSet(messages):
        /\ msg.type = LiftJson
        /\ msg.action = Validate
        /\
            LET
                User == msg.to
                Lift == lifts[User][msg.liftGuid]
                Referee == msg.referee
                FoilPeer == PrevElemIn(User, Lift.route)
                StockPeer == NextElemIn(User, Lift.route)
            IN
                /\ msg.from = Referee
                /\ User = Lift.originator
                /\ Lift.state = Seek
                /\ msg.route = Lift.route
                /\ msg.liftType = Lift.liftType
                /\ msg.originator = Lift.originator
                /\ msg.destination = Lift.destination
                /\ msg.value = Lift.value
                /\ lifts' = [lifts EXCEPT ![User] = [@ EXCEPT ![msg.liftGuid] = [@ EXCEPT !.state = Good]]]
                /\ tallies' =
                    [id \in DOMAIN tallies |->
                        CASE id = <<User, FoilPeer, Stock>> -> UpdateLiftChit(tallies[id], msg.liftGuid, Good)
                        [] id = <<User, StockPeer, Foil>> -> UpdateLiftChit(tallies[id], msg.liftGuid, Good)
                        [] OTHER -> tallies[id]]
                /\ messages' = messages
                    (-) SetToBag({msg})
                    (+) SetToBag({([from |-> User, to |-> StockPeer, type |-> LiftJson, action |-> Commit, liftGuid |-> msg.liftGuid])})
    /\ UNCHANGED <<tallies, paymentsRemaining, linearLiftsRemaining, nextGuid>>
    /\ _stateNum' = Print("CommitLift", _stateNum + 1)

HandleLiftCommit ==
    /\ \E msg \in BagToSet(messages):
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
                    (+) SetToBag({([from |-> User, to |-> StockPeer, type |-> LiftJson, action |-> Commit, liftGuid |-> msg.liftGuid])})
    /\ UNCHANGED <<paymentsRemaining, linearLiftsRemaining, nextGuid>>
    /\ _stateNum' = Print("HandleLiftCommit", _stateNum + 1)

HandleLiftCommitLoopback ==
    /\ \E msg \in BagToSet(messages):
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
    /\ UNCHANGED <<tallies, lifts, paymentsRemaining, linearLiftsRemaining, nextGuid>>
    /\ _stateNum' = Print("HandleLiftCommitLoopback", _stateNum + 1)

(*** Time Control ***)

Tick ==
    /\ _stateNum < NewStateLimit \* Make state space finite
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
    \*\/ TimeOutInvoice
    \/ ProposeCircularLift
    \/ ProposeLinearLift
    \/ HandleLiftProposal
    \/ IgnoreTimedOutLiftProposal
    \/ IgnoreTimedOutLiftTerminus
    \*\/ AskTimeOutLift
    \/ HandleLiftTimeout
    \/ HandleUnknownLiftTimeout
    \/ HandleLiftTimeoutLoopback
    \/ HandleLiftValidation
    \/ RequestLiftValidation
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
    \*/\ SF_vars(TimeOutInvoice)
    /\ SF_vars(ProposeCircularLift)
    /\ SF_vars(ProposeLinearLift)
    /\ SF_vars(HandleLiftProposal)
    /\ WF_vars(IgnoreTimedOutLiftProposal)
    /\ WF_vars(IgnoreTimedOutLiftTerminus)
    \*/\ SF_vars(AskTimeOutLift)
    /\ SF_vars(HandleLiftTimeout)
    /\ SF_vars(HandleUnknownLiftTimeout)
    /\ WF_vars(HandleLiftTimeoutLoopback)
    /\ WF_vars(HandleLiftValidation) \* check wf is good
    /\ WF_vars(RequestLiftValidation) \* check wf is good
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
