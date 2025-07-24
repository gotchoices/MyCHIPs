---------------------------- MODULE ChipNetBasic ----------------------------
(*
ChipNet Basic Lift Protocol Specification

This specification models the ChipNet-based lift protocol, building upon
historical MyCHIPs formal verification work:

- DSR Analysis (2020): Found safety/liveness tradeoffs in original protocol
- BYU Analysis: Verified single-referee protocol using SPIN + Coq + TLA+
- This Model: ChipNet flexible consensus with Byzantine fault tolerance

Key ChipNet Features:
- Variable referee sets (single referee to multiple external referees)
- Participant-chosen consensus mechanisms
- Byzantine fault tolerance for minority honest nodes
- Circuit starvation attack resistance via Insurance Chit Protocol

Historical Model References:
- ../dsr/phase-1/spec/ - Original lift mechanics and safety/liveness issues
- ../byu/tla/ - Single referee consensus verification patterns
- ../byu/spin/ - 2-entity base case verification approach
*)

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
    Nodes,           \* Set of all nodes in the network
    Links,           \* Set of directed credit relationships: Links ⊆ Nodes × Nodes  
    MaxLiftValue,    \* Maximum value for any lift
    RefereeNodes,    \* Set of potential external referees (can overlap with Nodes)
    ByzantineNodes   \* Set of Byzantine (malicious) nodes ⊆ Nodes

VARIABLES
    tallies,         \* Node credit balances: [nodeA][nodeB] → balance 
    lifts,           \* Active lifts: liftId → lift_record
    messages,        \* Network messages in transit
    nodeStates       \* Per-node protocol state

vars == <<tallies, lifts, messages, nodeStates>>

(* ================ TYPE DEFINITIONS ================ *)

\* Lift states following historical DSR/BYU models
LiftStates == {"Seek", "Pend", "Good", "Void", "Timeout"}

\* Message types extending BYU referee interaction patterns
MessageTypes == {
    "LiftProposal",      \* Propose lift along route
    "LiftAccept",        \* Accept participation in lift
    "LiftReject",        \* Reject participation in lift
    "RefereePoll",       \* Poll referee for decision
    "RefereeDecision",   \* Referee commit/void decision
    "LiftCommit",        \* Propagate commit decision
    "LiftVoid",          \* Propagate void decision
    "InsuranceRequest",  \* Request insurance chit (NEW for ChipNet)
    "InsuranceGrant",    \* Grant insurance chit (NEW for ChipNet)
    "ResolutionRequest", \* Request resolution chit (NEW for ChipNet)
    "ResolutionGrant"    \* Grant resolution chit (NEW for ChipNet)
}

\* ChipNet consensus mechanisms (NEW capability)
ConsensusMechanisms == {
    "SingleReferee",     \* Compatible with BYU single-referee analysis
    "MultiReferee",      \* Multiple external referees vote
    "ParticipantVote",   \* Lift participants vote directly
    "HybridConsensus"    \* Mix of referees and participants
}

(* ================ HELPER PREDICATES ================ *)

\* Check if a node is honest (not Byzantine)
HonestNode(node) == node \notin ByzantineNodes

\* Check if majority of referees are honest for a given lift
HonestMajority(refereeSet) == 
    Cardinality({r \in refereeSet : HonestNode(r)}) > Cardinality(refereeSet) ÷ 2

\* Get neighboring nodes in the lift route
NextInRoute(node, route) == 
    IF \E i \in 1..(Len(route)-1) : route[i] = node 
    THEN route[CHOOSE i \in 1..(Len(route)-1) : route[i] = node] + 1]
    ELSE CHOOSE x \in Nodes : FALSE \* Invalid if node not in route

PrevInRoute(node, route) == 
    IF \E i \in 2..Len(route) : route[i] = node 
    THEN route[CHOOSE i \in 2..Len(route) : route[i] = node] - 1]
    ELSE CHOOSE x \in Nodes : FALSE \* Invalid if node not in route

(* ================ INITIALIZATION ================ *)

TypeInvariant ==
    /\ tallies \in [Nodes → [Nodes → Int]]  \* Credit balances between nodes
    /\ lifts \in [SUBSET STRING → RECORD]   \* Lift records keyed by ID
    /\ messages \in SUBSET RECORD           \* Network message set
    /\ nodeStates \in [Nodes → RECORD]      \* Per-node state

Init ==
    /\ tallies = [n1 \in Nodes |-> [n2 \in Nodes |-> 0]]  \* Initialize all balances to zero
    /\ lifts = [liftId \in {} |-> []]  \* No active lifts initially
    /\ messages = {}  \* No messages in transit
    /\ nodeStates = [n \in Nodes |-> [
        activeLiftIds: {},
        promisedChits: {},
        insuranceChits: {},
        resolutionChits: {}
    ]]

(* ================ CORE ACTIONS ================ *)

\* A node proposes a lift along a discovered route
\* Builds on DSR lift proposal mechanics, adds ChipNet consensus selection
ProposeLift(originator, route, value, consensus, referees) ==
    /\ originator \in Nodes
    /\ value \in 1..MaxLiftValue
    /\ Len(route) >= 2
    /\ route[1] = originator
    /\ consensus \in ConsensusMechanisms
    /\ CASE consensus = "SingleReferee" → Cardinality(referees) = 1
         [] consensus = "MultiReferee" → Cardinality(referees) > 1
         [] consensus = "ParticipantVote" → referees = {}
         [] consensus = "HybridConsensus" → Cardinality(referees) >= 1
    /\ LET liftId == "lift_" \o ToString(Cardinality(lifts) + 1)
           liftRecord == [
               id: liftId,
               originator: originator,
               route: route,
               value: value,
               state: "Seek",
               consensus: consensus,
               referees: referees,
               promises: {},
               decisions: {}
           ]
       IN /\ lifts' = lifts @@ (liftId :> liftRecord)
          /\ messages' = messages \cup {[
              type: "LiftProposal",
              from: originator,
              to: route[2],  \* Send to next node in route
              liftId: liftId,
              route: route,
              value: value,
              consensus: consensus,
              referees: referees
          ]}
          /\ UNCHANGED <<tallies, nodeStates>>

\* A node handles an incoming lift proposal
\* Extends BYU acceptance/rejection patterns with ChipNet considerations
HandleLiftProposal(node, msg) ==
    /\ msg.type = "LiftProposal"
    /\ msg.to = node
    /\ msg.liftId \in DOMAIN lifts
    /\ lifts[msg.liftId].state = "Seek"
    /\ LET lift == lifts[msg.liftId]
           position == CHOOSE i \in 1..Len(lift.route) : lift.route[i] = node
           canParticipate == HonestNode(node) \* Honest nodes follow protocol
       IN IF canParticipate
          THEN \* Accept and forward or complete the proposal
               /\ IF position = Len(lift.route)  \* Last node in route
                  THEN \* Complete the circuit/line - start consensus
                       /\ lifts' = [lifts EXCEPT ![msg.liftId].state = "Pend"]
                       /\ messages' = (messages \ {msg}) \cup 
                          {[type: "RefereePoll", 
                            from: node, 
                            to: CHOOSE ref \in lift.referees : TRUE,
                            liftId: msg.liftId]}
                  ELSE \* Forward to next node
                       /\ lifts' = [lifts EXCEPT ![msg.liftId].promises = 
                                    @ \cup {[node: node, promised: TRUE]}]
                       /\ messages' = (messages \ {msg}) \cup 
                          {[type: "LiftProposal",
                            from: node,
                            to: lift.route[position + 1],
                            liftId: msg.liftId,
                            route: lift.route,
                            value: lift.value,
                            consensus: lift.consensus,
                            referees: lift.referees]}
               /\ UNCHANGED <<tallies, nodeStates>>
          ELSE \* Reject (Byzantine behavior or resource constraints)
               /\ messages' = (messages \ {msg}) \cup 
                  {[type: "LiftReject", 
                    from: node, 
                    to: msg.from, 
                    liftId: msg.liftId]}
               /\ UNCHANGED <<tallies, lifts, nodeStates>>

\* Referee makes a decision on a lift
\* Based on BYU referee patterns, extended for ChipNet multi-referee scenarios
RefereeDecision(referee, liftId, decision) ==
    /\ referee \in RefereeNodes
    /\ liftId \in DOMAIN lifts
    /\ lifts[liftId].state = "Pend"
    /\ decision \in {"Commit", "Void"}
    /\ LET lift == lifts[liftId]
           isHonestDecision == HonestNode(referee) \* Honest referees decide fairly
           finalDecision == IF isHonestDecision THEN decision ELSE "Void"  \* Byzantine referees void
       IN /\ lifts' = [lifts EXCEPT ![liftId].decisions = 
                       @ \cup {[referee: referee, decision: finalDecision]}]
          /\ messages' = messages \cup 
             {[type: "RefereeDecision", 
               from: referee, 
               to: lift.originator, 
               liftId: liftId, 
               decision: finalDecision]}
          /\ UNCHANGED <<tallies, nodeStates>>

(* ================ INSURANCE CHIT PROTOCOL (NEW) ================ *)

\* Request insurance chit to neutralize promised resources
\* NEW: Circuit starvation attack mitigation
RequestInsuranceChit(node, peer, liftId) ==
    /\ node \in Nodes /\ peer \in Nodes
    /\ liftId \in DOMAIN lifts
    /\ lifts[liftId].state = "Pend"  \* Lift is hung
    /\ HonestNode(node) /\ HonestNode(peer)  \* Both nodes are honest
    /\ \* TODO: Add timeout condition - lift has been pending for too long
    /\ messages' = messages \cup 
       {[type: "InsuranceRequest", 
         from: node, 
         to: peer, 
         liftId: liftId]}
    /\ UNCHANGED <<tallies, lifts, nodeStates>>

\* Grant insurance chit to neutralize effect of promised resources
GrantInsuranceChit(node, requestor, liftId) ==
    /\ \E msg \in messages : 
       /\ msg.type = "InsuranceRequest"
       /\ msg.from = requestor /\ msg.to = node
       /\ msg.liftId = liftId
    /\ HonestNode(node)  \* Only honest nodes grant insurance
    /\ LET insuranceChit == [
           originator: requestor,
           target: node,
           liftId: liftId,
           direction: "Opposite",  \* Opposite direction to promised chit
           state: "Promised"       \* Tied to original lift fate
       ]
       IN /\ nodeStates' = [nodeStates EXCEPT 
              ![node].insuranceChits = @ \cup {insuranceChit}]
          /\ messages' = (messages \ {CHOOSE msg \in messages : 
                          msg.type = "InsuranceRequest" /\ 
                          msg.from = requestor /\ msg.to = node}) \cup
                         {[type: "InsuranceGrant", 
                           from: node, 
                           to: requestor, 
                           liftId: liftId]}
          /\ UNCHANGED <<tallies, lifts>>

(* ================ SAFETY PROPERTIES ================ *)

\* No node loses credits inappropriately (from DSR safety analysis)
BalancePreservation == 
    \A n1, n2 \in Nodes : 
        tallies[n1][n2] + tallies[n2][n1] = 0  \* Symmetric credit relationships

\* All lifts eventually reach a final state (from BYU liveness analysis)
LiftProgression == 
    \A liftId \in DOMAIN lifts :
        lifts[liftId].state \in {"Seek", "Pend"} ~> 
        lifts[liftId].state \in {"Good", "Void", "Timeout"}

\* NEW: Insurance chits provide net zero effect
InsuranceNeutrality ==
    \A node \in Nodes, liftId \in DOMAIN lifts :
        \A chit \in nodeStates[node].insuranceChits :
            chit.liftId = liftId => 
                \* Insurance chit value cancels promised chit value
                "NetEffectZero"  \* TODO: Formalize the balance calculation

(* ================ BYZANTINE FAULT TOLERANCE ================ *)

\* System remains safe with minority Byzantine nodes
ByzantineTolerance ==
    Cardinality(ByzantineNodes) < Cardinality(Nodes) ÷ 2 =>
        /\ BalancePreservation
        /\ LiftProgression
        /\ InsuranceNeutrality

\* NEW: Circuit starvation attacks fail to permanently harm honest nodes
CircuitStarvationResistance ==
    \A liftId \in DOMAIN lifts :
        /\ lifts[liftId].state = "Pend"  \* Lift is hung
        /\ Cardinality(ByzantineNodes \cap DOMAIN lifts[liftId].promises) > 
           Cardinality(Nodes \ ByzantineNodes \cap DOMAIN lifts[liftId].promises)
        => \* Honest minority can recover via insurance chits
           <> \A honest \in (Nodes \ ByzantineNodes) :
               \* Honest nodes can continue trading normally
               "CanContinueTrading"  \* TODO: Formalize trading capability

(* ================ NEXT STATE RELATION ================ *)

Next ==
    \/ \E originator \in Nodes, route \in Seq(Nodes), value \in 1..MaxLiftValue,
         consensus \in ConsensusMechanisms, referees \in SUBSET RefereeNodes :
         ProposeLift(originator, route, value, consensus, referees)
    \/ \E node \in Nodes, msg \in messages :
         HandleLiftProposal(node, msg)
    \/ \E referee \in RefereeNodes, liftId \in DOMAIN lifts, decision \in {"Commit", "Void"} :
         RefereeDecision(referee, liftId, decision)
    \/ \E node, peer \in Nodes, liftId \in DOMAIN lifts :
         RequestInsuranceChit(node, peer, liftId)
    \/ \E node, requestor \in Nodes, liftId \in DOMAIN lifts :
         GrantInsuranceChit(node, requestor, liftId)

(* ================ SPECIFICATION ================ *)

Spec == Init /\ [][Next]_vars

\* Fairness conditions ensuring progress
Fairness == 
    /\ \A node \in Nodes : WF_vars(\E msg \in messages : HandleLiftProposal(node, msg))
    /\ \A referee \in RefereeNodes : WF_vars(\E liftId \in DOMAIN lifts, decision \in {"Commit", "Void"} : 
                                              RefereeDecision(referee, liftId, decision))

FairSpec == Spec /\ Fairness

(* ================ MODEL VALIDATION ================ *)

\* Properties to verify in TLC model checker
THEOREM Spec => []TypeInvariant
THEOREM FairSpec => []BalancePreservation  
THEOREM FairSpec => []LiftProgression
THEOREM FairSpec => []ByzantineTolerance

(*
TODO: Complete the specification with:
1. Detailed balance calculations for insurance/resolution chits
2. Timeout handling and detection mechanisms  
3. Network partition scenarios and recovery
4. Complete circuit starvation attack modeling
5. Integration with historical DSR/BYU property definitions
6. Comprehensive Byzantine behavior modeling
*)

==== 