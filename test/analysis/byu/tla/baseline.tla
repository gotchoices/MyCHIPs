------------------------------ MODULE baseline ------------------------------
EXTENDS Integers, Sequences, TLC

CONSTANTS MESSAGES_FAIL

A == "A"
B == "B"
C == "C"
D == "D"

NextIndexIn(i, ring) == (i % Len(ring)) + 1  \* 1 indexed between 1 and length

PrevIndexIn(i, ring) == ((i - 2) % Len(ring)) + 1 \* -2 +1 to get correctly in 1 ... len
\* not sure why this is not 0 indexed. I assume personal preferences

NextElemIn(elem, ring) == \*syntactic sugar to get next element in cycle using User not index
    LET I == CHOOSE i \in 1..Len(ring): ring[i] = elem
    IN ring[NextIndexIn(I, ring)]

PrevElemIn(elem, ring) == \*syntactic sugar to get previous element in cycle using User not index
    LET I == CHOOSE i \in 1..Len(ring): ring[i] = elem
    IN ring[PrevIndexIn(I, ring)]

InitTallyBalance(id) == IF id = <<"D", "A", "Foil">> THEN -20 ELSE
                        IF id = <<"A", "D", "Stock">> THEN 20 ELSE
                        IF id[3] = "Foil" THEN -100 ELSE 100
InitTallyProjBalance(id) == IF id = <<"D", "A", "Foil">> THEN -20 ELSE
                        IF id = <<"A", "D", "Stock">> THEN 20 ELSE
                        IF id[3] = "Foil" THEN -100 ELSE 100

Min(s) == CHOOSE x \in s: \A y \in s: y >= x

Values(f) == {f[x]: x \in DOMAIN f}

MaxLiftValueFor(route, tallies) == 
Min(Values([foilId \in {id \in DOMAIN tallies:
        \E i \in DOMAIN route: <<route[i], route[NextIndexIn(i, route)], "Foil">> = id}
                    |-> -tallies[foilId].balance]))

TalliesOfType(tallies, type) == [id \in {id \in DOMAIN tallies: id[3] = type} |-> tallies[id]] \* gets all tallies of a given type

NoConversationBetween(x, y, messages, readMessages) == ~\E msg \in messages : msg \notin readMessages /\ {msg.from, msg.to} = {x, y}


(* --algorithm LiftProtocol
variables 
    Users = {A, B, C, D},
    LiftProposers = {A},
    Links = {<<A, B>>, <<B, C>>, <<C, D>>, <<C, A>>, <<D, A>>},
    Cycles = {<<A, B, C>>},
	tallies = [id \in UNION{{<<x, y, "Foil">>, <<y, x, "Stock">>}: <<x, y>> \in Links} |-> [balance |-> InitTallyBalance(id), projectedBalance |-> InitTallyProjBalance(id) ]],
    messages = {},
    readMessages = {},
    lifts = [user \in Users |-> [id \in {} |-> 0]], \* init empty map
    nextLiftGuid = 1,

macro printLater(item) begin
    printBuffer := Append(printBuffer, item);
end macro;

macro sendMessage(message) begin
    if MESSAGES_FAIL then
        with messageWorks \in {TRUE, FALSE} do
            if messageWorks then
                messages := UNION{messages, message};
            else
                printLater("Message Failed");
                messages := UNION{messages, message};
                readMessages := UNION{readMessages, message}
            end if
        end with;
    else 
        messages := UNION{messages, message};
    end if
end macro;


procedure ProposeLift (proposer, cycle, liftValue)
    variables
        nextPeer,
        liftGuid,
begin
ProposeLift:
	printLater("Proposing Lift");
    prevPeer := PrevElemIn(proposer, cycle);
    liftGuid := nextLiftGuid;
    nextLiftGuid := nextLiftGuid + 1;
    lifts[proposer] := liftGuid :> [originator |-> proposer, value |-> liftValue, state |-> "Seek", route |-> route];
    tallies[<<proposer, prevPeer, "Stock">>].projectedBalance := tallies[<<proposer, prevPeer, "Stock">>].projectedBalance - liftValue;
    lsm: sendMessage( {[liftId |-> liftGuid, originator |-> proposer, from |-> proposer, to |-> prevPeer, type |-> "LiftJSON", route |-> cycle, value |-> liftValue]});
	PLR: return;
end procedure

procedure HandleLift (from, to, route, liftValue, originator, liftId)
    variables
        prevPeer,
begin
HandleLift:
	printLater("Handling Lift");
    prevPeer := PrevElemIn(to, route);
        lifts[to] := liftId :> [originator |-> originator, value |-> liftValue, state |-> "Seek", route |-> route];
        tallies[<<to, from, "Foil">>].projectedBalance := tallies[<<to, from, "Foil">>].projectedBalance + liftValue;
    if to /= originator then
        L1: tallies[<<to, prevPeer, "Stock">>].projectedBalance := tallies[<<to, prevPeer, "Stock">>].projectedBalance - liftValue;
        lsm: sendMessage({[liftId |-> liftId, originator |-> originator, from |-> to, to |-> prevPeer, type |-> "LiftJSON", route |-> route, value |-> liftValue]});
    else
        call ValidateLift(to, liftId)
    end if;
    HLR: return;
end procedure

procedure ValidateLift (originator, liftId)
    variables
        prevPeer,
        timeout,
begin
ValidateLift:
        printLater("Validating Lift");
        prevPeer := NextElemIn(originator, lifts[originator][liftId].route);
        with timeoutDecision \in {TRUE, FALSE} do
            timeout := timeoutDecision;
        end with;
        if timeout then
            lpt: printLater("Lift Timeout");
            lifts[originator][liftId].state := "Timeout";
            messages := UNION{messages, {[liftId |-> liftId, from |-> originator, to |-> prevPeer, type |-> "LiftTimeoutJSON"]}};
            L1: tallies[<<originator, prevPeer, "Foil">>].projectedBalance := tallies[<<originator, prevPeer, "Foil">>].projectedBalance - lifts[originator][liftId].value;
        else
            lpv: printLater("Lift Valid");
            lifts[originator][liftId].state := "Good";
            lsm: sendMessage({[liftId |-> liftId, from |-> originator, to |-> prevPeer, type |-> "LiftCommitJSON"]});
            L2: tallies[<<originator, prevPeer, "Foil">>].balance := tallies[<<originator, prevPeer, "Foil">>].balance + lifts[originator][liftId].value;
        end if;
        VLR: return;
end procedure

procedure CommitLift (from, to, liftId)
    variables
        nextPeer,
        liftValue,
begin
CommitLift:
	printLater("Committing Lift");
    liftValue := lifts[to][liftId].value;
    lifts[to][liftId].state := "Good";
    CL2: tallies[<<to, from, "Stock">>].balance := tallies[<<to, from, "Stock">>].balance - liftValue;
    if to /= lifts[to][liftId].originator then
        nextPeer := NextElemIn(to, lifts[to][liftId].route);
        CL4: sendMessage({[liftId |-> liftId, from |-> to, to |-> nextPeer, type |-> "LiftCommitJSON"]});
        CL3: tallies[<<to, nextPeer, "Foil">>].balance := tallies[<<to, nextPeer, "Foil">>].balance + liftValue;
    end if;
    CLR: return;
end procedure

procedure TimeoutLift (from, to, liftId)
    variables
        nextPeer,
        liftValue,
begin
TimeoutLift:
	printLater("Timeout Lift");
    liftValue := lifts[to][liftId].value;
    lifts[to][liftId].state := "Fail";
    CL2: tallies[<<to, from, "Stock">>].projectedBalance := tallies[<<to, from, "Stock">>].projectedBalance + liftValue;
    if to /= lifts[to][liftId].originator then
        nextPeer := NextElemIn(to, lifts[to][liftId].route);
        CL4: sendMessage({[liftId |-> liftId, from |-> to, to |-> nextPeer, type |-> "LiftTimeoutJSON"]});
        CL3: tallies[<<to, nextPeer, "Foil">>].projectedBalance := tallies[<<to, nextPeer, "Foil">>].projectedBalance - liftValue;
    end if;
    CLR: return;
end procedure

procedure CheckTimeout (toCheck)
    variables
begin
CheckTimeout:
	printLater("Check Timeout");
    CTR: return;
end procedure

process procId \in Users \* one process for now
    variables
        cycle,
        liftValue,
        toAct,
        printBuffer = <<>>,
begin
ProcStart:
    printLater("Start");
    l1: printLater(self);
    if self \in LiftProposers then
        cycle := CHOOSE c \in Cycles : c[1] = self; \* pick a cycle
        liftValue := MaxLiftValueFor(cycle, tallies);
        call ProposeLift(self, cycle, liftValue);
    end if;
    l2: await messages /= {}; \* wait for the first message to pop in the bag
    l2w: while messages \ readMessages /= {} do
    l3: await (messages \ readMessages = {} \/ (\E message \in messages: message \notin readMessages /\ message.to = self));
    if messages \ readMessages /= {} then
        toAct := CHOOSE message \in messages: message \notin readMessages /\ message.to = self;
        if toAct.type = "LiftJSON" then
            call HandleLift(toAct.from, toAct.to, toAct.route, toAct.value, toAct.originator, toAct.liftId) ;
        end if;
        l5: if toAct.type = "LiftCommitJSON" then
            call CommitLift(toAct.from, toAct.to, toAct.liftId)
        end if;
        l6: if toAct.type = "LiftTimeoutJSON" then
            call TimeoutLift(toAct.from, toAct.to, toAct.liftId)
        end if;
        l4: readMessages := UNION{readMessages, {toAct}};
    end if;
    end while;
    (*print readMessages;
    print lifts;
    print tallies;
    *)
    lpb: print printBuffer
end process


end algorithm *)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-533c7e0e8ae1bbf22d307acdfa49b92c
\* Label ProposeLift of procedure ProposeLift at line 58 col 5 changed to ProposeLift_
\* Label lsm of procedure ProposeLift at line 62 col 5 changed to lsm_
\* Label HandleLift of procedure HandleLift at line 58 col 5 changed to HandleLift_
\* Label L1 of procedure HandleLift at line 104 col 13 changed to L1_
\* Label lsm of procedure HandleLift at line 62 col 5 changed to lsm_H
\* Label ValidateLift of procedure ValidateLift at line 58 col 5 changed to ValidateLift_
\* Label CommitLift of procedure CommitLift at line 58 col 5 changed to CommitLift_
\* Label CL2 of procedure CommitLift at line 146 col 10 changed to CL2_
\* Label CL4 of procedure CommitLift at line 62 col 5 changed to CL4_
\* Label CL3 of procedure CommitLift at line 150 col 14 changed to CL3_
\* Label CLR of procedure CommitLift at line 152 col 10 changed to CLR_
\* Label TimeoutLift of procedure TimeoutLift at line 58 col 5 changed to TimeoutLift_
\* Label CheckTimeout of procedure CheckTimeout at line 58 col 5 changed to CheckTimeout_
\* Process variable cycle of process procId at line 183 col 9 changed to cycle_
\* Process variable liftValue of process procId at line 184 col 9 changed to liftValue_
\* Procedure variable nextPeer of procedure ProposeLift at line 80 col 9 changed to nextPeer_
\* Procedure variable prevPeer of procedure HandleLift at line 96 col 9 changed to prevPeer_
\* Procedure variable nextPeer of procedure CommitLift at line 139 col 9 changed to nextPeer_C
\* Procedure variable liftValue of procedure CommitLift at line 140 col 9 changed to liftValue_C
\* Procedure variable liftValue of procedure TimeoutLift at line 158 col 9 changed to liftValue_T
\* Parameter liftValue of procedure ProposeLift at line 78 col 41 changed to liftValue_P
\* Parameter from of procedure HandleLift at line 94 col 23 changed to from_
\* Parameter to of procedure HandleLift at line 94 col 29 changed to to_
\* Parameter originator of procedure HandleLift at line 94 col 51 changed to originator_
\* Parameter liftId of procedure HandleLift at line 94 col 63 changed to liftId_
\* Parameter liftId of procedure ValidateLift at line 112 col 37 changed to liftId_V
\* Parameter from of procedure CommitLift at line 137 col 23 changed to from_C
\* Parameter to of procedure CommitLift at line 137 col 29 changed to to_C
\* Parameter liftId of procedure CommitLift at line 137 col 33 changed to liftId_C
CONSTANT defaultInitValue
VARIABLES Users, LiftProposers, Links, Cycles, tallies, messages, 
          readMessages, lifts, nextLiftGuid, pc, stack, proposer, cycle, 
          liftValue_P, nextPeer_, liftGuid, from_, to_, route, liftValue, 
          originator_, liftId_, prevPeer_, originator, liftId_V, prevPeer, 
          timeout, from_C, to_C, liftId_C, nextPeer_C, liftValue_C, from, to, 
          liftId, nextPeer, liftValue_T, toCheck, cycle_, liftValue_, toAct, 
          printBuffer

vars == << Users, LiftProposers, Links, Cycles, tallies, messages, 
           readMessages, lifts, nextLiftGuid, pc, stack, proposer, cycle, 
           liftValue_P, nextPeer_, liftGuid, from_, to_, route, liftValue, 
           originator_, liftId_, prevPeer_, originator, liftId_V, prevPeer, 
           timeout, from_C, to_C, liftId_C, nextPeer_C, liftValue_C, from, to, 
           liftId, nextPeer, liftValue_T, toCheck, cycle_, liftValue_, toAct, 
           printBuffer >>

ProcSet == (Users)

Init == (* Global variables *)
        /\ Users = {A, B, C, D}
        /\ LiftProposers = {A}
        /\ Links = {<<A, B>>, <<B, C>>, <<C, D>>, <<C, A>>, <<D, A>>}
        /\ Cycles = {<<A, B, C>>}
        /\ tallies = [id \in UNION{{<<x, y, "Foil">>, <<y, x, "Stock">>}: <<x, y>> \in Links} |-> [balance |-> InitTallyBalance(id), projectedBalance |-> InitTallyProjBalance(id) ]]
        /\ messages = {}
        /\ readMessages = {}
        /\ lifts = [user \in Users |-> [id \in {} |-> 0]]
        /\ nextLiftGuid = 1
        (* Procedure ProposeLift *)
        /\ proposer = [ self \in ProcSet |-> defaultInitValue]
        /\ cycle = [ self \in ProcSet |-> defaultInitValue]
        /\ liftValue_P = [ self \in ProcSet |-> defaultInitValue]
        /\ nextPeer_ = [ self \in ProcSet |-> defaultInitValue]
        /\ liftGuid = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure HandleLift *)
        /\ from_ = [ self \in ProcSet |-> defaultInitValue]
        /\ to_ = [ self \in ProcSet |-> defaultInitValue]
        /\ route = [ self \in ProcSet |-> defaultInitValue]
        /\ liftValue = [ self \in ProcSet |-> defaultInitValue]
        /\ originator_ = [ self \in ProcSet |-> defaultInitValue]
        /\ liftId_ = [ self \in ProcSet |-> defaultInitValue]
        /\ prevPeer_ = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure ValidateLift *)
        /\ originator = [ self \in ProcSet |-> defaultInitValue]
        /\ liftId_V = [ self \in ProcSet |-> defaultInitValue]
        /\ prevPeer = [ self \in ProcSet |-> defaultInitValue]
        /\ timeout = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure CommitLift *)
        /\ from_C = [ self \in ProcSet |-> defaultInitValue]
        /\ to_C = [ self \in ProcSet |-> defaultInitValue]
        /\ liftId_C = [ self \in ProcSet |-> defaultInitValue]
        /\ nextPeer_C = [ self \in ProcSet |-> defaultInitValue]
        /\ liftValue_C = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure TimeoutLift *)
        /\ from = [ self \in ProcSet |-> defaultInitValue]
        /\ to = [ self \in ProcSet |-> defaultInitValue]
        /\ liftId = [ self \in ProcSet |-> defaultInitValue]
        /\ nextPeer = [ self \in ProcSet |-> defaultInitValue]
        /\ liftValue_T = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure CheckTimeout *)
        /\ toCheck = [ self \in ProcSet |-> defaultInitValue]
        (* Process procId *)
        /\ cycle_ = [self \in Users |-> defaultInitValue]
        /\ liftValue_ = [self \in Users |-> defaultInitValue]
        /\ toAct = [self \in Users |-> defaultInitValue]
        /\ printBuffer = [self \in Users |-> <<>>]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "ProcStart"]

ProposeLift_(self) == /\ pc[self] = "ProposeLift_"
                      /\ printBuffer' = [printBuffer EXCEPT ![self] = Append(printBuffer[self], "Proposing Lift")]
                      /\ prevPeer' = [prevPeer EXCEPT ![self] = PrevElemIn(proposer[self], cycle[self])]
                      /\ liftGuid' = [liftGuid EXCEPT ![self] = nextLiftGuid]
                      /\ nextLiftGuid' = nextLiftGuid + 1
                      /\ lifts' = [lifts EXCEPT ![proposer[self]] = liftGuid'[self] :> [originator |-> proposer[self], value |-> liftValue_P[self], state |-> "Seek", route |-> route[self]]]
                      /\ tallies' = [tallies EXCEPT ![<<proposer[self], prevPeer'[self], "Stock">>].projectedBalance = tallies[<<proposer[self], prevPeer'[self], "Stock">>].projectedBalance - liftValue_P[self]]
                      /\ pc' = [pc EXCEPT ![self] = "lsm_"]
                      /\ UNCHANGED << Users, LiftProposers, Links, Cycles, 
                                      messages, readMessages, stack, proposer, 
                                      cycle, liftValue_P, nextPeer_, from_, 
                                      to_, route, liftValue, originator_, 
                                      liftId_, prevPeer_, originator, liftId_V, 
                                      timeout, from_C, to_C, liftId_C, 
                                      nextPeer_C, liftValue_C, from, to, 
                                      liftId, nextPeer, liftValue_T, toCheck, 
                                      cycle_, liftValue_, toAct >>

lsm_(self) == /\ pc[self] = "lsm_"
              /\ IF MESSAGES_FAIL
                    THEN /\ \E messageWorks \in {TRUE, FALSE}:
                              IF messageWorks
                                 THEN /\ messages' = UNION{messages, ({[liftId |-> liftGuid[self], originator |-> proposer[self], from |-> proposer[self], to |-> prevPeer[self], type |-> "LiftJSON", route |-> cycle[self], value |-> liftValue_P[self]]})}
                                      /\ UNCHANGED << readMessages, 
                                                      printBuffer >>
                                 ELSE /\ printBuffer' = [printBuffer EXCEPT ![self] = Append(printBuffer[self], "Message Failed")]
                                      /\ messages' = UNION{messages, ({[liftId |-> liftGuid[self], originator |-> proposer[self], from |-> proposer[self], to |-> prevPeer[self], type |-> "LiftJSON", route |-> cycle[self], value |-> liftValue_P[self]]})}
                                      /\ readMessages' = UNION{readMessages, ({[liftId |-> liftGuid[self], originator |-> proposer[self], from |-> proposer[self], to |-> prevPeer[self], type |-> "LiftJSON", route |-> cycle[self], value |-> liftValue_P[self]]})}
                    ELSE /\ messages' = UNION{messages, ({[liftId |-> liftGuid[self], originator |-> proposer[self], from |-> proposer[self], to |-> prevPeer[self], type |-> "LiftJSON", route |-> cycle[self], value |-> liftValue_P[self]]})}
                         /\ UNCHANGED << readMessages, printBuffer >>
              /\ pc' = [pc EXCEPT ![self] = "PLR"]
              /\ UNCHANGED << Users, LiftProposers, Links, Cycles, tallies, 
                              lifts, nextLiftGuid, stack, proposer, cycle, 
                              liftValue_P, nextPeer_, liftGuid, from_, to_, 
                              route, liftValue, originator_, liftId_, 
                              prevPeer_, originator, liftId_V, prevPeer, 
                              timeout, from_C, to_C, liftId_C, nextPeer_C, 
                              liftValue_C, from, to, liftId, nextPeer, 
                              liftValue_T, toCheck, cycle_, liftValue_, toAct >>

PLR(self) == /\ pc[self] = "PLR"
             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
             /\ nextPeer_' = [nextPeer_ EXCEPT ![self] = Head(stack[self]).nextPeer_]
             /\ liftGuid' = [liftGuid EXCEPT ![self] = Head(stack[self]).liftGuid]
             /\ proposer' = [proposer EXCEPT ![self] = Head(stack[self]).proposer]
             /\ cycle' = [cycle EXCEPT ![self] = Head(stack[self]).cycle]
             /\ liftValue_P' = [liftValue_P EXCEPT ![self] = Head(stack[self]).liftValue_P]
             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
             /\ UNCHANGED << Users, LiftProposers, Links, Cycles, tallies, 
                             messages, readMessages, lifts, nextLiftGuid, 
                             from_, to_, route, liftValue, originator_, 
                             liftId_, prevPeer_, originator, liftId_V, 
                             prevPeer, timeout, from_C, to_C, liftId_C, 
                             nextPeer_C, liftValue_C, from, to, liftId, 
                             nextPeer, liftValue_T, toCheck, cycle_, 
                             liftValue_, toAct, printBuffer >>

ProposeLift(self) == ProposeLift_(self) \/ lsm_(self) \/ PLR(self)

HandleLift_(self) == /\ pc[self] = "HandleLift_"
                     /\ printBuffer' = [printBuffer EXCEPT ![self] = Append(printBuffer[self], "Handling Lift")]
                     /\ prevPeer_' = [prevPeer_ EXCEPT ![self] = PrevElemIn(to_[self], route[self])]
                     /\ lifts' = [lifts EXCEPT ![to_[self]] = liftId_[self] :> [originator |-> originator_[self], value |-> liftValue[self], state |-> "Seek", route |-> route[self]]]
                     /\ tallies' = [tallies EXCEPT ![<<to_[self], from_[self], "Foil">>].projectedBalance = tallies[<<to_[self], from_[self], "Foil">>].projectedBalance + liftValue[self]]
                     /\ IF to_[self] /= originator_[self]
                           THEN /\ pc' = [pc EXCEPT ![self] = "L1_"]
                                /\ UNCHANGED << stack, originator, liftId_V, 
                                                prevPeer, timeout >>
                           ELSE /\ /\ liftId_V' = [liftId_V EXCEPT ![self] = liftId_[self]]
                                   /\ originator' = [originator EXCEPT ![self] = to_[self]]
                                   /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "ValidateLift",
                                                                            pc        |->  "HLR",
                                                                            prevPeer  |->  prevPeer[self],
                                                                            timeout   |->  timeout[self],
                                                                            originator |->  originator[self],
                                                                            liftId_V  |->  liftId_V[self] ] >>
                                                                        \o stack[self]]
                                /\ prevPeer' = [prevPeer EXCEPT ![self] = defaultInitValue]
                                /\ timeout' = [timeout EXCEPT ![self] = defaultInitValue]
                                /\ pc' = [pc EXCEPT ![self] = "ValidateLift_"]
                     /\ UNCHANGED << Users, LiftProposers, Links, Cycles, 
                                     messages, readMessages, nextLiftGuid, 
                                     proposer, cycle, liftValue_P, nextPeer_, 
                                     liftGuid, from_, to_, route, liftValue, 
                                     originator_, liftId_, from_C, to_C, 
                                     liftId_C, nextPeer_C, liftValue_C, from, 
                                     to, liftId, nextPeer, liftValue_T, 
                                     toCheck, cycle_, liftValue_, toAct >>

L1_(self) == /\ pc[self] = "L1_"
             /\ tallies' = [tallies EXCEPT ![<<to_[self], prevPeer_[self], "Stock">>].projectedBalance = tallies[<<to_[self], prevPeer_[self], "Stock">>].projectedBalance - liftValue[self]]
             /\ pc' = [pc EXCEPT ![self] = "lsm_H"]
             /\ UNCHANGED << Users, LiftProposers, Links, Cycles, messages, 
                             readMessages, lifts, nextLiftGuid, stack, 
                             proposer, cycle, liftValue_P, nextPeer_, liftGuid, 
                             from_, to_, route, liftValue, originator_, 
                             liftId_, prevPeer_, originator, liftId_V, 
                             prevPeer, timeout, from_C, to_C, liftId_C, 
                             nextPeer_C, liftValue_C, from, to, liftId, 
                             nextPeer, liftValue_T, toCheck, cycle_, 
                             liftValue_, toAct, printBuffer >>

lsm_H(self) == /\ pc[self] = "lsm_H"
               /\ IF MESSAGES_FAIL
                     THEN /\ \E messageWorks \in {TRUE, FALSE}:
                               IF messageWorks
                                  THEN /\ messages' = UNION{messages, ({[liftId |-> liftId_[self], originator |-> originator_[self], from |-> to_[self], to |-> prevPeer_[self], type |-> "LiftJSON", route |-> route[self], value |-> liftValue[self]]})}
                                       /\ UNCHANGED << readMessages, 
                                                       printBuffer >>
                                  ELSE /\ printBuffer' = [printBuffer EXCEPT ![self] = Append(printBuffer[self], "Message Failed")]
                                       /\ messages' = UNION{messages, ({[liftId |-> liftId_[self], originator |-> originator_[self], from |-> to_[self], to |-> prevPeer_[self], type |-> "LiftJSON", route |-> route[self], value |-> liftValue[self]]})}
                                       /\ readMessages' = UNION{readMessages, ({[liftId |-> liftId_[self], originator |-> originator_[self], from |-> to_[self], to |-> prevPeer_[self], type |-> "LiftJSON", route |-> route[self], value |-> liftValue[self]]})}
                     ELSE /\ messages' = UNION{messages, ({[liftId |-> liftId_[self], originator |-> originator_[self], from |-> to_[self], to |-> prevPeer_[self], type |-> "LiftJSON", route |-> route[self], value |-> liftValue[self]]})}
                          /\ UNCHANGED << readMessages, printBuffer >>
               /\ pc' = [pc EXCEPT ![self] = "HLR"]
               /\ UNCHANGED << Users, LiftProposers, Links, Cycles, tallies, 
                               lifts, nextLiftGuid, stack, proposer, cycle, 
                               liftValue_P, nextPeer_, liftGuid, from_, to_, 
                               route, liftValue, originator_, liftId_, 
                               prevPeer_, originator, liftId_V, prevPeer, 
                               timeout, from_C, to_C, liftId_C, nextPeer_C, 
                               liftValue_C, from, to, liftId, nextPeer, 
                               liftValue_T, toCheck, cycle_, liftValue_, toAct >>

HLR(self) == /\ pc[self] = "HLR"
             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
             /\ prevPeer_' = [prevPeer_ EXCEPT ![self] = Head(stack[self]).prevPeer_]
             /\ from_' = [from_ EXCEPT ![self] = Head(stack[self]).from_]
             /\ to_' = [to_ EXCEPT ![self] = Head(stack[self]).to_]
             /\ route' = [route EXCEPT ![self] = Head(stack[self]).route]
             /\ liftValue' = [liftValue EXCEPT ![self] = Head(stack[self]).liftValue]
             /\ originator_' = [originator_ EXCEPT ![self] = Head(stack[self]).originator_]
             /\ liftId_' = [liftId_ EXCEPT ![self] = Head(stack[self]).liftId_]
             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
             /\ UNCHANGED << Users, LiftProposers, Links, Cycles, tallies, 
                             messages, readMessages, lifts, nextLiftGuid, 
                             proposer, cycle, liftValue_P, nextPeer_, liftGuid, 
                             originator, liftId_V, prevPeer, timeout, from_C, 
                             to_C, liftId_C, nextPeer_C, liftValue_C, from, to, 
                             liftId, nextPeer, liftValue_T, toCheck, cycle_, 
                             liftValue_, toAct, printBuffer >>

HandleLift(self) == HandleLift_(self) \/ L1_(self) \/ lsm_H(self)
                       \/ HLR(self)

ValidateLift_(self) == /\ pc[self] = "ValidateLift_"
                       /\ printBuffer' = [printBuffer EXCEPT ![self] = Append(printBuffer[self], "Validating Lift")]
                       /\ prevPeer' = [prevPeer EXCEPT ![self] = NextElemIn(originator[self], lifts[originator[self]][liftId_V[self]].route)]
                       /\ \E timeoutDecision \in {TRUE, FALSE}:
                            timeout' = [timeout EXCEPT ![self] = timeoutDecision]
                       /\ IF timeout'[self]
                             THEN /\ pc' = [pc EXCEPT ![self] = "lpt"]
                             ELSE /\ pc' = [pc EXCEPT ![self] = "lpv"]
                       /\ UNCHANGED << Users, LiftProposers, Links, Cycles, 
                                       tallies, messages, readMessages, lifts, 
                                       nextLiftGuid, stack, proposer, cycle, 
                                       liftValue_P, nextPeer_, liftGuid, from_, 
                                       to_, route, liftValue, originator_, 
                                       liftId_, prevPeer_, originator, 
                                       liftId_V, from_C, to_C, liftId_C, 
                                       nextPeer_C, liftValue_C, from, to, 
                                       liftId, nextPeer, liftValue_T, toCheck, 
                                       cycle_, liftValue_, toAct >>

lpt(self) == /\ pc[self] = "lpt"
             /\ printBuffer' = [printBuffer EXCEPT ![self] = Append(printBuffer[self], "Lift Timeout")]
             /\ lifts' = [lifts EXCEPT ![originator[self]][liftId_V[self]].state = "Timeout"]
             /\ messages' = UNION{messages, {[liftId |-> liftId_V[self], from |-> originator[self], to |-> prevPeer[self], type |-> "LiftTimeoutJSON"]}}
             /\ pc' = [pc EXCEPT ![self] = "L1"]
             /\ UNCHANGED << Users, LiftProposers, Links, Cycles, tallies, 
                             readMessages, nextLiftGuid, stack, proposer, 
                             cycle, liftValue_P, nextPeer_, liftGuid, from_, 
                             to_, route, liftValue, originator_, liftId_, 
                             prevPeer_, originator, liftId_V, prevPeer, 
                             timeout, from_C, to_C, liftId_C, nextPeer_C, 
                             liftValue_C, from, to, liftId, nextPeer, 
                             liftValue_T, toCheck, cycle_, liftValue_, toAct >>

L1(self) == /\ pc[self] = "L1"
            /\ tallies' = [tallies EXCEPT ![<<originator[self], prevPeer[self], "Foil">>].projectedBalance = tallies[<<originator[self], prevPeer[self], "Foil">>].projectedBalance - lifts[originator[self]][liftId_V[self]].value]
            /\ pc' = [pc EXCEPT ![self] = "VLR"]
            /\ UNCHANGED << Users, LiftProposers, Links, Cycles, messages, 
                            readMessages, lifts, nextLiftGuid, stack, proposer, 
                            cycle, liftValue_P, nextPeer_, liftGuid, from_, 
                            to_, route, liftValue, originator_, liftId_, 
                            prevPeer_, originator, liftId_V, prevPeer, timeout, 
                            from_C, to_C, liftId_C, nextPeer_C, liftValue_C, 
                            from, to, liftId, nextPeer, liftValue_T, toCheck, 
                            cycle_, liftValue_, toAct, printBuffer >>

lpv(self) == /\ pc[self] = "lpv"
             /\ printBuffer' = [printBuffer EXCEPT ![self] = Append(printBuffer[self], "Lift Valid")]
             /\ lifts' = [lifts EXCEPT ![originator[self]][liftId_V[self]].state = "Good"]
             /\ pc' = [pc EXCEPT ![self] = "lsm"]
             /\ UNCHANGED << Users, LiftProposers, Links, Cycles, tallies, 
                             messages, readMessages, nextLiftGuid, stack, 
                             proposer, cycle, liftValue_P, nextPeer_, liftGuid, 
                             from_, to_, route, liftValue, originator_, 
                             liftId_, prevPeer_, originator, liftId_V, 
                             prevPeer, timeout, from_C, to_C, liftId_C, 
                             nextPeer_C, liftValue_C, from, to, liftId, 
                             nextPeer, liftValue_T, toCheck, cycle_, 
                             liftValue_, toAct >>

lsm(self) == /\ pc[self] = "lsm"
             /\ IF MESSAGES_FAIL
                   THEN /\ \E messageWorks \in {TRUE, FALSE}:
                             IF messageWorks
                                THEN /\ messages' = UNION{messages, ({[liftId |-> liftId_V[self], from |-> originator[self], to |-> prevPeer[self], type |-> "LiftCommitJSON"]})}
                                     /\ UNCHANGED << readMessages, printBuffer >>
                                ELSE /\ printBuffer' = [printBuffer EXCEPT ![self] = Append(printBuffer[self], "Message Failed")]
                                     /\ messages' = UNION{messages, ({[liftId |-> liftId_V[self], from |-> originator[self], to |-> prevPeer[self], type |-> "LiftCommitJSON"]})}
                                     /\ readMessages' = UNION{readMessages, ({[liftId |-> liftId_V[self], from |-> originator[self], to |-> prevPeer[self], type |-> "LiftCommitJSON"]})}
                   ELSE /\ messages' = UNION{messages, ({[liftId |-> liftId_V[self], from |-> originator[self], to |-> prevPeer[self], type |-> "LiftCommitJSON"]})}
                        /\ UNCHANGED << readMessages, printBuffer >>
             /\ pc' = [pc EXCEPT ![self] = "L2"]
             /\ UNCHANGED << Users, LiftProposers, Links, Cycles, tallies, 
                             lifts, nextLiftGuid, stack, proposer, cycle, 
                             liftValue_P, nextPeer_, liftGuid, from_, to_, 
                             route, liftValue, originator_, liftId_, prevPeer_, 
                             originator, liftId_V, prevPeer, timeout, from_C, 
                             to_C, liftId_C, nextPeer_C, liftValue_C, from, to, 
                             liftId, nextPeer, liftValue_T, toCheck, cycle_, 
                             liftValue_, toAct >>

L2(self) == /\ pc[self] = "L2"
            /\ tallies' = [tallies EXCEPT ![<<originator[self], prevPeer[self], "Foil">>].balance = tallies[<<originator[self], prevPeer[self], "Foil">>].balance + lifts[originator[self]][liftId_V[self]].value]
            /\ pc' = [pc EXCEPT ![self] = "VLR"]
            /\ UNCHANGED << Users, LiftProposers, Links, Cycles, messages, 
                            readMessages, lifts, nextLiftGuid, stack, proposer, 
                            cycle, liftValue_P, nextPeer_, liftGuid, from_, 
                            to_, route, liftValue, originator_, liftId_, 
                            prevPeer_, originator, liftId_V, prevPeer, timeout, 
                            from_C, to_C, liftId_C, nextPeer_C, liftValue_C, 
                            from, to, liftId, nextPeer, liftValue_T, toCheck, 
                            cycle_, liftValue_, toAct, printBuffer >>

VLR(self) == /\ pc[self] = "VLR"
             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
             /\ prevPeer' = [prevPeer EXCEPT ![self] = Head(stack[self]).prevPeer]
             /\ timeout' = [timeout EXCEPT ![self] = Head(stack[self]).timeout]
             /\ originator' = [originator EXCEPT ![self] = Head(stack[self]).originator]
             /\ liftId_V' = [liftId_V EXCEPT ![self] = Head(stack[self]).liftId_V]
             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
             /\ UNCHANGED << Users, LiftProposers, Links, Cycles, tallies, 
                             messages, readMessages, lifts, nextLiftGuid, 
                             proposer, cycle, liftValue_P, nextPeer_, liftGuid, 
                             from_, to_, route, liftValue, originator_, 
                             liftId_, prevPeer_, from_C, to_C, liftId_C, 
                             nextPeer_C, liftValue_C, from, to, liftId, 
                             nextPeer, liftValue_T, toCheck, cycle_, 
                             liftValue_, toAct, printBuffer >>

ValidateLift(self) == ValidateLift_(self) \/ lpt(self) \/ L1(self)
                         \/ lpv(self) \/ lsm(self) \/ L2(self) \/ VLR(self)

CommitLift_(self) == /\ pc[self] = "CommitLift_"
                     /\ printBuffer' = [printBuffer EXCEPT ![self] = Append(printBuffer[self], "Committing Lift")]
                     /\ liftValue_C' = [liftValue_C EXCEPT ![self] = lifts[to_C[self]][liftId_C[self]].value]
                     /\ lifts' = [lifts EXCEPT ![to_C[self]][liftId_C[self]].state = "Good"]
                     /\ pc' = [pc EXCEPT ![self] = "CL2_"]
                     /\ UNCHANGED << Users, LiftProposers, Links, Cycles, 
                                     tallies, messages, readMessages, 
                                     nextLiftGuid, stack, proposer, cycle, 
                                     liftValue_P, nextPeer_, liftGuid, from_, 
                                     to_, route, liftValue, originator_, 
                                     liftId_, prevPeer_, originator, liftId_V, 
                                     prevPeer, timeout, from_C, to_C, liftId_C, 
                                     nextPeer_C, from, to, liftId, nextPeer, 
                                     liftValue_T, toCheck, cycle_, liftValue_, 
                                     toAct >>

CL2_(self) == /\ pc[self] = "CL2_"
              /\ tallies' = [tallies EXCEPT ![<<to_C[self], from_C[self], "Stock">>].balance = tallies[<<to_C[self], from_C[self], "Stock">>].balance - liftValue_C[self]]
              /\ IF to_C[self] /= lifts[to_C[self]][liftId_C[self]].originator
                    THEN /\ nextPeer_C' = [nextPeer_C EXCEPT ![self] = NextElemIn(to_C[self], lifts[to_C[self]][liftId_C[self]].route)]
                         /\ pc' = [pc EXCEPT ![self] = "CL4_"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "CLR_"]
                         /\ UNCHANGED nextPeer_C
              /\ UNCHANGED << Users, LiftProposers, Links, Cycles, messages, 
                              readMessages, lifts, nextLiftGuid, stack, 
                              proposer, cycle, liftValue_P, nextPeer_, 
                              liftGuid, from_, to_, route, liftValue, 
                              originator_, liftId_, prevPeer_, originator, 
                              liftId_V, prevPeer, timeout, from_C, to_C, 
                              liftId_C, liftValue_C, from, to, liftId, 
                              nextPeer, liftValue_T, toCheck, cycle_, 
                              liftValue_, toAct, printBuffer >>

CL4_(self) == /\ pc[self] = "CL4_"
              /\ IF MESSAGES_FAIL
                    THEN /\ \E messageWorks \in {TRUE, FALSE}:
                              IF messageWorks
                                 THEN /\ messages' = UNION{messages, ({[liftId |-> liftId_C[self], from |-> to_C[self], to |-> nextPeer_C[self], type |-> "LiftCommitJSON"]})}
                                      /\ UNCHANGED << readMessages, 
                                                      printBuffer >>
                                 ELSE /\ printBuffer' = [printBuffer EXCEPT ![self] = Append(printBuffer[self], "Message Failed")]
                                      /\ messages' = UNION{messages, ({[liftId |-> liftId_C[self], from |-> to_C[self], to |-> nextPeer_C[self], type |-> "LiftCommitJSON"]})}
                                      /\ readMessages' = UNION{readMessages, ({[liftId |-> liftId_C[self], from |-> to_C[self], to |-> nextPeer_C[self], type |-> "LiftCommitJSON"]})}
                    ELSE /\ messages' = UNION{messages, ({[liftId |-> liftId_C[self], from |-> to_C[self], to |-> nextPeer_C[self], type |-> "LiftCommitJSON"]})}
                         /\ UNCHANGED << readMessages, printBuffer >>
              /\ pc' = [pc EXCEPT ![self] = "CL3_"]
              /\ UNCHANGED << Users, LiftProposers, Links, Cycles, tallies, 
                              lifts, nextLiftGuid, stack, proposer, cycle, 
                              liftValue_P, nextPeer_, liftGuid, from_, to_, 
                              route, liftValue, originator_, liftId_, 
                              prevPeer_, originator, liftId_V, prevPeer, 
                              timeout, from_C, to_C, liftId_C, nextPeer_C, 
                              liftValue_C, from, to, liftId, nextPeer, 
                              liftValue_T, toCheck, cycle_, liftValue_, toAct >>

CL3_(self) == /\ pc[self] = "CL3_"
              /\ tallies' = [tallies EXCEPT ![<<to_C[self], nextPeer_C[self], "Foil">>].balance = tallies[<<to_C[self], nextPeer_C[self], "Foil">>].balance + liftValue_C[self]]
              /\ pc' = [pc EXCEPT ![self] = "CLR_"]
              /\ UNCHANGED << Users, LiftProposers, Links, Cycles, messages, 
                              readMessages, lifts, nextLiftGuid, stack, 
                              proposer, cycle, liftValue_P, nextPeer_, 
                              liftGuid, from_, to_, route, liftValue, 
                              originator_, liftId_, prevPeer_, originator, 
                              liftId_V, prevPeer, timeout, from_C, to_C, 
                              liftId_C, nextPeer_C, liftValue_C, from, to, 
                              liftId, nextPeer, liftValue_T, toCheck, cycle_, 
                              liftValue_, toAct, printBuffer >>

CLR_(self) == /\ pc[self] = "CLR_"
              /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
              /\ nextPeer_C' = [nextPeer_C EXCEPT ![self] = Head(stack[self]).nextPeer_C]
              /\ liftValue_C' = [liftValue_C EXCEPT ![self] = Head(stack[self]).liftValue_C]
              /\ from_C' = [from_C EXCEPT ![self] = Head(stack[self]).from_C]
              /\ to_C' = [to_C EXCEPT ![self] = Head(stack[self]).to_C]
              /\ liftId_C' = [liftId_C EXCEPT ![self] = Head(stack[self]).liftId_C]
              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
              /\ UNCHANGED << Users, LiftProposers, Links, Cycles, tallies, 
                              messages, readMessages, lifts, nextLiftGuid, 
                              proposer, cycle, liftValue_P, nextPeer_, 
                              liftGuid, from_, to_, route, liftValue, 
                              originator_, liftId_, prevPeer_, originator, 
                              liftId_V, prevPeer, timeout, from, to, liftId, 
                              nextPeer, liftValue_T, toCheck, cycle_, 
                              liftValue_, toAct, printBuffer >>

CommitLift(self) == CommitLift_(self) \/ CL2_(self) \/ CL4_(self)
                       \/ CL3_(self) \/ CLR_(self)

TimeoutLift_(self) == /\ pc[self] = "TimeoutLift_"
                      /\ printBuffer' = [printBuffer EXCEPT ![self] = Append(printBuffer[self], "Timeout Lift")]
                      /\ liftValue_T' = [liftValue_T EXCEPT ![self] = lifts[to[self]][liftId[self]].value]
                      /\ lifts' = [lifts EXCEPT ![to[self]][liftId[self]].state = "Fail"]
                      /\ pc' = [pc EXCEPT ![self] = "CL2"]
                      /\ UNCHANGED << Users, LiftProposers, Links, Cycles, 
                                      tallies, messages, readMessages, 
                                      nextLiftGuid, stack, proposer, cycle, 
                                      liftValue_P, nextPeer_, liftGuid, from_, 
                                      to_, route, liftValue, originator_, 
                                      liftId_, prevPeer_, originator, liftId_V, 
                                      prevPeer, timeout, from_C, to_C, 
                                      liftId_C, nextPeer_C, liftValue_C, from, 
                                      to, liftId, nextPeer, toCheck, cycle_, 
                                      liftValue_, toAct >>

CL2(self) == /\ pc[self] = "CL2"
             /\ tallies' = [tallies EXCEPT ![<<to[self], from[self], "Stock">>].projectedBalance = tallies[<<to[self], from[self], "Stock">>].projectedBalance + liftValue_T[self]]
             /\ IF to[self] /= lifts[to[self]][liftId[self]].originator
                   THEN /\ nextPeer' = [nextPeer EXCEPT ![self] = NextElemIn(to[self], lifts[to[self]][liftId[self]].route)]
                        /\ pc' = [pc EXCEPT ![self] = "CL4"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "CLR"]
                        /\ UNCHANGED nextPeer
             /\ UNCHANGED << Users, LiftProposers, Links, Cycles, messages, 
                             readMessages, lifts, nextLiftGuid, stack, 
                             proposer, cycle, liftValue_P, nextPeer_, liftGuid, 
                             from_, to_, route, liftValue, originator_, 
                             liftId_, prevPeer_, originator, liftId_V, 
                             prevPeer, timeout, from_C, to_C, liftId_C, 
                             nextPeer_C, liftValue_C, from, to, liftId, 
                             liftValue_T, toCheck, cycle_, liftValue_, toAct, 
                             printBuffer >>

CL4(self) == /\ pc[self] = "CL4"
             /\ IF MESSAGES_FAIL
                   THEN /\ \E messageWorks \in {TRUE, FALSE}:
                             IF messageWorks
                                THEN /\ messages' = UNION{messages, ({[liftId |-> liftId[self], from |-> to[self], to |-> nextPeer[self], type |-> "LiftTimeoutJSON"]})}
                                     /\ UNCHANGED << readMessages, printBuffer >>
                                ELSE /\ printBuffer' = [printBuffer EXCEPT ![self] = Append(printBuffer[self], "Message Failed")]
                                     /\ messages' = UNION{messages, ({[liftId |-> liftId[self], from |-> to[self], to |-> nextPeer[self], type |-> "LiftTimeoutJSON"]})}
                                     /\ readMessages' = UNION{readMessages, ({[liftId |-> liftId[self], from |-> to[self], to |-> nextPeer[self], type |-> "LiftTimeoutJSON"]})}
                   ELSE /\ messages' = UNION{messages, ({[liftId |-> liftId[self], from |-> to[self], to |-> nextPeer[self], type |-> "LiftTimeoutJSON"]})}
                        /\ UNCHANGED << readMessages, printBuffer >>
             /\ pc' = [pc EXCEPT ![self] = "CL3"]
             /\ UNCHANGED << Users, LiftProposers, Links, Cycles, tallies, 
                             lifts, nextLiftGuid, stack, proposer, cycle, 
                             liftValue_P, nextPeer_, liftGuid, from_, to_, 
                             route, liftValue, originator_, liftId_, prevPeer_, 
                             originator, liftId_V, prevPeer, timeout, from_C, 
                             to_C, liftId_C, nextPeer_C, liftValue_C, from, to, 
                             liftId, nextPeer, liftValue_T, toCheck, cycle_, 
                             liftValue_, toAct >>

CL3(self) == /\ pc[self] = "CL3"
             /\ tallies' = [tallies EXCEPT ![<<to[self], nextPeer[self], "Foil">>].projectedBalance = tallies[<<to[self], nextPeer[self], "Foil">>].projectedBalance - liftValue_T[self]]
             /\ pc' = [pc EXCEPT ![self] = "CLR"]
             /\ UNCHANGED << Users, LiftProposers, Links, Cycles, messages, 
                             readMessages, lifts, nextLiftGuid, stack, 
                             proposer, cycle, liftValue_P, nextPeer_, liftGuid, 
                             from_, to_, route, liftValue, originator_, 
                             liftId_, prevPeer_, originator, liftId_V, 
                             prevPeer, timeout, from_C, to_C, liftId_C, 
                             nextPeer_C, liftValue_C, from, to, liftId, 
                             nextPeer, liftValue_T, toCheck, cycle_, 
                             liftValue_, toAct, printBuffer >>

CLR(self) == /\ pc[self] = "CLR"
             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
             /\ nextPeer' = [nextPeer EXCEPT ![self] = Head(stack[self]).nextPeer]
             /\ liftValue_T' = [liftValue_T EXCEPT ![self] = Head(stack[self]).liftValue_T]
             /\ from' = [from EXCEPT ![self] = Head(stack[self]).from]
             /\ to' = [to EXCEPT ![self] = Head(stack[self]).to]
             /\ liftId' = [liftId EXCEPT ![self] = Head(stack[self]).liftId]
             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
             /\ UNCHANGED << Users, LiftProposers, Links, Cycles, tallies, 
                             messages, readMessages, lifts, nextLiftGuid, 
                             proposer, cycle, liftValue_P, nextPeer_, liftGuid, 
                             from_, to_, route, liftValue, originator_, 
                             liftId_, prevPeer_, originator, liftId_V, 
                             prevPeer, timeout, from_C, to_C, liftId_C, 
                             nextPeer_C, liftValue_C, toCheck, cycle_, 
                             liftValue_, toAct, printBuffer >>

TimeoutLift(self) == TimeoutLift_(self) \/ CL2(self) \/ CL4(self)
                        \/ CL3(self) \/ CLR(self)

CheckTimeout_(self) == /\ pc[self] = "CheckTimeout_"
                       /\ printBuffer' = [printBuffer EXCEPT ![self] = Append(printBuffer[self], "Check Timeout")]
                       /\ pc' = [pc EXCEPT ![self] = "CTR"]
                       /\ UNCHANGED << Users, LiftProposers, Links, Cycles, 
                                       tallies, messages, readMessages, lifts, 
                                       nextLiftGuid, stack, proposer, cycle, 
                                       liftValue_P, nextPeer_, liftGuid, from_, 
                                       to_, route, liftValue, originator_, 
                                       liftId_, prevPeer_, originator, 
                                       liftId_V, prevPeer, timeout, from_C, 
                                       to_C, liftId_C, nextPeer_C, liftValue_C, 
                                       from, to, liftId, nextPeer, liftValue_T, 
                                       toCheck, cycle_, liftValue_, toAct >>

CTR(self) == /\ pc[self] = "CTR"
             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
             /\ toCheck' = [toCheck EXCEPT ![self] = Head(stack[self]).toCheck]
             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
             /\ UNCHANGED << Users, LiftProposers, Links, Cycles, tallies, 
                             messages, readMessages, lifts, nextLiftGuid, 
                             proposer, cycle, liftValue_P, nextPeer_, liftGuid, 
                             from_, to_, route, liftValue, originator_, 
                             liftId_, prevPeer_, originator, liftId_V, 
                             prevPeer, timeout, from_C, to_C, liftId_C, 
                             nextPeer_C, liftValue_C, from, to, liftId, 
                             nextPeer, liftValue_T, cycle_, liftValue_, toAct, 
                             printBuffer >>

CheckTimeout(self) == CheckTimeout_(self) \/ CTR(self)

ProcStart(self) == /\ pc[self] = "ProcStart"
                   /\ printBuffer' = [printBuffer EXCEPT ![self] = Append(printBuffer[self], "Start")]
                   /\ pc' = [pc EXCEPT ![self] = "l1"]
                   /\ UNCHANGED << Users, LiftProposers, Links, Cycles, 
                                   tallies, messages, readMessages, lifts, 
                                   nextLiftGuid, stack, proposer, cycle, 
                                   liftValue_P, nextPeer_, liftGuid, from_, 
                                   to_, route, liftValue, originator_, liftId_, 
                                   prevPeer_, originator, liftId_V, prevPeer, 
                                   timeout, from_C, to_C, liftId_C, nextPeer_C, 
                                   liftValue_C, from, to, liftId, nextPeer, 
                                   liftValue_T, toCheck, cycle_, liftValue_, 
                                   toAct >>

l1(self) == /\ pc[self] = "l1"
            /\ printBuffer' = [printBuffer EXCEPT ![self] = Append(printBuffer[self], self)]
            /\ IF self \in LiftProposers
                  THEN /\ cycle_' = [cycle_ EXCEPT ![self] = CHOOSE c \in Cycles : c[1] = self]
                       /\ liftValue_' = [liftValue_ EXCEPT ![self] = MaxLiftValueFor(cycle_'[self], tallies)]
                       /\ /\ cycle' = [cycle EXCEPT ![self] = cycle_'[self]]
                          /\ liftValue_P' = [liftValue_P EXCEPT ![self] = liftValue_'[self]]
                          /\ proposer' = [proposer EXCEPT ![self] = self]
                          /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "ProposeLift",
                                                                   pc        |->  "l2",
                                                                   nextPeer_ |->  nextPeer_[self],
                                                                   liftGuid  |->  liftGuid[self],
                                                                   proposer  |->  proposer[self],
                                                                   cycle     |->  cycle[self],
                                                                   liftValue_P |->  liftValue_P[self] ] >>
                                                               \o stack[self]]
                       /\ nextPeer_' = [nextPeer_ EXCEPT ![self] = defaultInitValue]
                       /\ liftGuid' = [liftGuid EXCEPT ![self] = defaultInitValue]
                       /\ pc' = [pc EXCEPT ![self] = "ProposeLift_"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "l2"]
                       /\ UNCHANGED << stack, proposer, cycle, liftValue_P, 
                                       nextPeer_, liftGuid, cycle_, liftValue_ >>
            /\ UNCHANGED << Users, LiftProposers, Links, Cycles, tallies, 
                            messages, readMessages, lifts, nextLiftGuid, from_, 
                            to_, route, liftValue, originator_, liftId_, 
                            prevPeer_, originator, liftId_V, prevPeer, timeout, 
                            from_C, to_C, liftId_C, nextPeer_C, liftValue_C, 
                            from, to, liftId, nextPeer, liftValue_T, toCheck, 
                            toAct >>

l2(self) == /\ pc[self] = "l2"
            /\ messages /= {}
            /\ pc' = [pc EXCEPT ![self] = "l2w"]
            /\ UNCHANGED << Users, LiftProposers, Links, Cycles, tallies, 
                            messages, readMessages, lifts, nextLiftGuid, stack, 
                            proposer, cycle, liftValue_P, nextPeer_, liftGuid, 
                            from_, to_, route, liftValue, originator_, liftId_, 
                            prevPeer_, originator, liftId_V, prevPeer, timeout, 
                            from_C, to_C, liftId_C, nextPeer_C, liftValue_C, 
                            from, to, liftId, nextPeer, liftValue_T, toCheck, 
                            cycle_, liftValue_, toAct, printBuffer >>

l2w(self) == /\ pc[self] = "l2w"
             /\ IF messages \ readMessages /= {}
                   THEN /\ pc' = [pc EXCEPT ![self] = "l3"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "lpb"]
             /\ UNCHANGED << Users, LiftProposers, Links, Cycles, tallies, 
                             messages, readMessages, lifts, nextLiftGuid, 
                             stack, proposer, cycle, liftValue_P, nextPeer_, 
                             liftGuid, from_, to_, route, liftValue, 
                             originator_, liftId_, prevPeer_, originator, 
                             liftId_V, prevPeer, timeout, from_C, to_C, 
                             liftId_C, nextPeer_C, liftValue_C, from, to, 
                             liftId, nextPeer, liftValue_T, toCheck, cycle_, 
                             liftValue_, toAct, printBuffer >>

l3(self) == /\ pc[self] = "l3"
            /\ (messages \ readMessages = {} \/ (\E message \in messages: message \notin readMessages /\ message.to = self))
            /\ IF messages \ readMessages /= {}
                  THEN /\ toAct' = [toAct EXCEPT ![self] = CHOOSE message \in messages: message \notin readMessages /\ message.to = self]
                       /\ IF toAct'[self].type = "LiftJSON"
                             THEN /\ /\ from_' = [from_ EXCEPT ![self] = toAct'[self].from]
                                     /\ liftId_' = [liftId_ EXCEPT ![self] = toAct'[self].liftId]
                                     /\ liftValue' = [liftValue EXCEPT ![self] = toAct'[self].value]
                                     /\ originator_' = [originator_ EXCEPT ![self] = toAct'[self].originator]
                                     /\ route' = [route EXCEPT ![self] = toAct'[self].route]
                                     /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "HandleLift",
                                                                              pc        |->  "l5",
                                                                              prevPeer_ |->  prevPeer_[self],
                                                                              from_     |->  from_[self],
                                                                              to_       |->  to_[self],
                                                                              route     |->  route[self],
                                                                              liftValue |->  liftValue[self],
                                                                              originator_ |->  originator_[self],
                                                                              liftId_   |->  liftId_[self] ] >>
                                                                          \o stack[self]]
                                     /\ to_' = [to_ EXCEPT ![self] = toAct'[self].to]
                                  /\ prevPeer_' = [prevPeer_ EXCEPT ![self] = defaultInitValue]
                                  /\ pc' = [pc EXCEPT ![self] = "HandleLift_"]
                             ELSE /\ pc' = [pc EXCEPT ![self] = "l5"]
                                  /\ UNCHANGED << stack, from_, to_, route, 
                                                  liftValue, originator_, 
                                                  liftId_, prevPeer_ >>
                  ELSE /\ pc' = [pc EXCEPT ![self] = "l2w"]
                       /\ UNCHANGED << stack, from_, to_, route, liftValue, 
                                       originator_, liftId_, prevPeer_, toAct >>
            /\ UNCHANGED << Users, LiftProposers, Links, Cycles, tallies, 
                            messages, readMessages, lifts, nextLiftGuid, 
                            proposer, cycle, liftValue_P, nextPeer_, liftGuid, 
                            originator, liftId_V, prevPeer, timeout, from_C, 
                            to_C, liftId_C, nextPeer_C, liftValue_C, from, to, 
                            liftId, nextPeer, liftValue_T, toCheck, cycle_, 
                            liftValue_, printBuffer >>

l5(self) == /\ pc[self] = "l5"
            /\ IF toAct[self].type = "LiftCommitJSON"
                  THEN /\ /\ from_C' = [from_C EXCEPT ![self] = toAct[self].from]
                          /\ liftId_C' = [liftId_C EXCEPT ![self] = toAct[self].liftId]
                          /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "CommitLift",
                                                                   pc        |->  "l6",
                                                                   nextPeer_C |->  nextPeer_C[self],
                                                                   liftValue_C |->  liftValue_C[self],
                                                                   from_C    |->  from_C[self],
                                                                   to_C      |->  to_C[self],
                                                                   liftId_C  |->  liftId_C[self] ] >>
                                                               \o stack[self]]
                          /\ to_C' = [to_C EXCEPT ![self] = toAct[self].to]
                       /\ nextPeer_C' = [nextPeer_C EXCEPT ![self] = defaultInitValue]
                       /\ liftValue_C' = [liftValue_C EXCEPT ![self] = defaultInitValue]
                       /\ pc' = [pc EXCEPT ![self] = "CommitLift_"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "l6"]
                       /\ UNCHANGED << stack, from_C, to_C, liftId_C, 
                                       nextPeer_C, liftValue_C >>
            /\ UNCHANGED << Users, LiftProposers, Links, Cycles, tallies, 
                            messages, readMessages, lifts, nextLiftGuid, 
                            proposer, cycle, liftValue_P, nextPeer_, liftGuid, 
                            from_, to_, route, liftValue, originator_, liftId_, 
                            prevPeer_, originator, liftId_V, prevPeer, timeout, 
                            from, to, liftId, nextPeer, liftValue_T, toCheck, 
                            cycle_, liftValue_, toAct, printBuffer >>

l6(self) == /\ pc[self] = "l6"
            /\ IF toAct[self].type = "LiftTimeoutJSON"
                  THEN /\ /\ from' = [from EXCEPT ![self] = toAct[self].from]
                          /\ liftId' = [liftId EXCEPT ![self] = toAct[self].liftId]
                          /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "TimeoutLift",
                                                                   pc        |->  "l4",
                                                                   nextPeer  |->  nextPeer[self],
                                                                   liftValue_T |->  liftValue_T[self],
                                                                   from      |->  from[self],
                                                                   to        |->  to[self],
                                                                   liftId    |->  liftId[self] ] >>
                                                               \o stack[self]]
                          /\ to' = [to EXCEPT ![self] = toAct[self].to]
                       /\ nextPeer' = [nextPeer EXCEPT ![self] = defaultInitValue]
                       /\ liftValue_T' = [liftValue_T EXCEPT ![self] = defaultInitValue]
                       /\ pc' = [pc EXCEPT ![self] = "TimeoutLift_"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "l4"]
                       /\ UNCHANGED << stack, from, to, liftId, nextPeer, 
                                       liftValue_T >>
            /\ UNCHANGED << Users, LiftProposers, Links, Cycles, tallies, 
                            messages, readMessages, lifts, nextLiftGuid, 
                            proposer, cycle, liftValue_P, nextPeer_, liftGuid, 
                            from_, to_, route, liftValue, originator_, liftId_, 
                            prevPeer_, originator, liftId_V, prevPeer, timeout, 
                            from_C, to_C, liftId_C, nextPeer_C, liftValue_C, 
                            toCheck, cycle_, liftValue_, toAct, printBuffer >>

l4(self) == /\ pc[self] = "l4"
            /\ readMessages' = UNION{readMessages, {toAct[self]}}
            /\ pc' = [pc EXCEPT ![self] = "l2w"]
            /\ UNCHANGED << Users, LiftProposers, Links, Cycles, tallies, 
                            messages, lifts, nextLiftGuid, stack, proposer, 
                            cycle, liftValue_P, nextPeer_, liftGuid, from_, 
                            to_, route, liftValue, originator_, liftId_, 
                            prevPeer_, originator, liftId_V, prevPeer, timeout, 
                            from_C, to_C, liftId_C, nextPeer_C, liftValue_C, 
                            from, to, liftId, nextPeer, liftValue_T, toCheck, 
                            cycle_, liftValue_, toAct, printBuffer >>

lpb(self) == /\ pc[self] = "lpb"
             /\ PrintT(printBuffer[self])
             /\ pc' = [pc EXCEPT ![self] = "Done"]
             /\ UNCHANGED << Users, LiftProposers, Links, Cycles, tallies, 
                             messages, readMessages, lifts, nextLiftGuid, 
                             stack, proposer, cycle, liftValue_P, nextPeer_, 
                             liftGuid, from_, to_, route, liftValue, 
                             originator_, liftId_, prevPeer_, originator, 
                             liftId_V, prevPeer, timeout, from_C, to_C, 
                             liftId_C, nextPeer_C, liftValue_C, from, to, 
                             liftId, nextPeer, liftValue_T, toCheck, cycle_, 
                             liftValue_, toAct, printBuffer >>

procId(self) == ProcStart(self) \/ l1(self) \/ l2(self) \/ l2w(self)
                   \/ l3(self) \/ l5(self) \/ l6(self) \/ l4(self)
                   \/ lpb(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet:  \/ ProposeLift(self) \/ HandleLift(self)
                               \/ ValidateLift(self) \/ CommitLift(self)
                               \/ TimeoutLift(self) \/ CheckTimeout(self))
           \/ (\E self \in Users: procId(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-55a2fcf30c836cbb5e45287b2fcfe901

RECURSIVE Sum(_)
Sum(f) ==
    IF DOMAIN f = {} THEN \* if there are no items left in the domain of the query
        0 \*the sum is 0
    ELSE \*otherwise
        LET X == CHOOSE x \in DOMAIN f: TRUE \* X is a function that returns an index to an arbitrary item in f
        IN f[X] + Sum([y \in DOMAIN f \ {X} |-> f[y]]) \* Add the arbitrary item to the Sum of f excluding X
\* y is a domain that has all of f except X. y is a set. f[y] is the set of all items excluding X.
\* Summary. Recursivly selects an item in f and adds it to the sum of f excluding that item

BalancesOfType(node, _tallies, type) == [id \in {id \in DOMAIN _tallies: id[1] = node /\ id[3] = type} |-> _tallies[id].balance] \* gets all tallies of a given type

AllBalances(node, _tallies) == [id \in {id \in DOMAIN _tallies: id[1] = node} |-> _tallies[id].balance] \* gets all tallies of a given type

StateSummary(node, _tallies) ==
	[
	 stockBalance |-> Sum(BalancesOfType(node, _tallies, "Stock")),
	 foilBalance |-> Sum(BalancesOfType(node, _tallies, "Foil")),
     totalBalance |-> Sum(AllBalances(node, _tallies))
    ]

BetterState(StateA, StateB) ==
    \/  StateA.totalBalance > StateB.totalBalance
    \/  (StateA.totalBalance = StateB.totalBalance /\ StateA.foilBalance > StateB.foilBalance)

LinkValid ==
    /\ Links \subseteq Users \X Users \* Links are a pair of users (user, user)
    /\ \A link \in Links: link[1] # link[2] \* Links don't connect to self (userA, userB) A != B


CycleValid == \A cycleV \in Cycles: \* for all cycles
    /\ \A i \in 1..Len(cycleV): cycleV[i] \in Users \* cycles are containers of only users
    /\ \A i, j \in 1..Len(cycleV): i # j => cycleV[i] # cycleV[j] \* no user appears twice in the cycle (this may be invalid)
    /\ \A i \in 1..Len(cycleV): <<cycleV[i], cycleV[NextIndexIn(i, cycleV)]>> \in Links \* every item in the cycle is linked with the next item
    \* need to ensure Links is symmetric

PartnersBalancesAreSymmetrical ==
    /\ \A <<x, y, type>> \in DOMAIN TalliesOfType(tallies, "Foil"):
        (
            /\ NoConversationBetween(x, y, messages, readMessages)
        ) => (
            /\ tallies[<<x, y, "Foil">>].balance = -tallies[<<y, x, "Stock">>].balance
            /\ tallies[<<x, y, "Foil">>].projectedBalance = -tallies[<<y, x, "Stock">>].projectedBalance
        )

PartnersBalancesAreSymmetricalInTheEnd ==
    \A <<x, y, type>> \in DOMAIN TalliesOfType(tallies, "Foil"):
        (
            /\ \A self \in ProcSet: pc[self] = "Done"
        ) => (
            /\ tallies[<<x, y, "Foil">>].balance = -tallies[<<y, x, "Stock">>].balance
            /\ tallies[<<x, y, "Foil">>].projectedBalance = -tallies[<<y, x, "Stock">>].projectedBalance
        )

PrintStateSummaries ==
    \A u \in Users:
        /\ PrintT(<<"State Summary", u, StateSummary(u, tallies)>>)
    



=============================================================================
\* Modification History
\* Last modified Sat Aug 22 16:46:43 MDT 2020 by kylestorey
\* Created Sat Aug 22 16:05:32 MDT 2020 by kylestorey
