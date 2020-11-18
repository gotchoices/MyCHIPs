------------------------------ MODULE liveness ------------------------------
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

NoConversationBetween(x, y, messages, doneMessages) == ~\E msg \in messages : msg \notin doneMessages /\ {msg.from, msg.to} = {x, y}

NotDone(lifts, users,  messages, doneMessages) ==
\/ \E user \in DOMAIN lifts : \E lid \in DOMAIN lifts[user] : lifts[user][lid].state = "Seek"
\/ \E x, y \in users : ~NoConversationBetween(x, y, messages, doneMessages)



(* --algorithm LiftProtocol
variables 
    Users = {A, B, C, D},
    LiftProposers = {A},
    ReliableUsers = {D},
    Links = {<<A, B>>, <<B, C>>, <<C, D>>, <<C, A>>, <<D, A>>},
    Cycles = {<<A, B, C>>},
	tallies = [id \in UNION{{<<x, y, "Foil">>, <<y, x, "Stock">>}: <<x, y>> \in Links} |-> [balance |-> InitTallyBalance(id), projectedBalance |-> InitTallyProjBalance(id) ]],
    messages = {},
    readMessages = {},
    lostMessages = {},
    lifts = [user \in Users |-> [id \in {} |-> 0]], \* init empty map
    startedNodes = {},
    nextLiftGuid = 1,

macro printLater(item) begin
    printBuffer := Append(printBuffer, item);
end macro;

macro sendMessage(message) begin
    if MESSAGES_FAIL then
        with messageWorks \in {TRUE, FALSE} do
            if messageWorks \/ message.to \in ReliableUsers \/ message.from \in ReliableUsers then
                messages := UNION{messages, {message}};
            else
                printLater("Message Failed");
                messages := UNION{messages, {message}};
                lostMessages := UNION{lostMessages, {message}}
            end if
        end with;
    else
        messages := UNION{messages, {message}};
    end if
end macro;


procedure ProposeLift (proposer, cycle, liftValue, arbitrator)
    variables
        nextPeer,
        liftGuid,
begin
ProposeLift:
	printLater("Proposing Lift");
    prevPeer := PrevElemIn(proposer, cycle);
    liftGuid := nextLiftGuid;
    nextLiftGuid := nextLiftGuid + 1;
    lifts[proposer] := liftGuid :> [originator |-> proposer, value |-> liftValue, state |-> "Seek", route |-> cycle, arbitrator |-> arbitrator];
    tallies[<<proposer, prevPeer, "Stock">>].projectedBalance := tallies[<<proposer, prevPeer, "Stock">>].projectedBalance - liftValue;
    lsm: sendMessage([liftId |-> liftGuid, originator |-> proposer, from |-> proposer, to |-> prevPeer, type |-> "LiftProposeJSON", route |-> cycle, value |-> liftValue, arbitrator |-> arbitrator]);
	PLR: return;
end procedure

procedure HandleLift (from, to, route, liftValue, originator, liftId, arbitrator)
    variables
        prevPeer,
begin
HandleLift:
	printLater("Handling Lift");
    prevPeer := PrevElemIn(to, route);
        lifts[to] := liftId :> [originator |-> originator, value |-> liftValue, state |-> "Seek", route |-> route, arbitrator |-> arbitrator];
        tallies[<<to, from, "Foil">>].projectedBalance := tallies[<<to, from, "Foil">>].projectedBalance + liftValue;
    if to /= originator then
        L1: tallies[<<to, prevPeer, "Stock">>].projectedBalance := tallies[<<to, prevPeer, "Stock">>].projectedBalance - liftValue;
        lsm: sendMessage([liftId |-> liftId, originator |-> originator, from |-> to, to |-> prevPeer, type |-> "LiftProposeJSON", route |-> route, value |-> liftValue, arbitrator |-> arbitrator]);
    else
        \* TODO Check to make sure the lift was not changed
        losm: sendMessage([liftId |-> liftId, originator |-> originator, from |-> to, to |-> arbitrator, type |-> "LiftValidateJSON", route |-> route, value |-> liftValue, arbitrator |-> arbitrator])
    end if;
    HLR: return;
end procedure

procedure DecideLiftValidity(from, to, route, liftValue, originator, liftId, arbitrator)
    variables
        result,
begin
DecideLiftValidity:
    printLater("Deciding Lift Validity");
    if liftId \notin DOMAIN lifts[arbitrator] \/ (liftId \in DOMAIN lifts[arbitrator] /\ lifts[arbitrator][liftId].state = "Seek") then
        if to = arbitrator then
            lchecktime: with validDecision \in {"Good", "Fail"} do
                result := validDecision;
            end with;
            if from = originator then
                lifts[arbitrator] := liftId :> [originator |-> originator, value |-> liftValue, state |-> result, route |-> route, arbitrator |-> arbitrator];
                lsm: sendMessage([from |-> to, to |-> from, type |-> "LiftValidResultJSON", liftId |-> liftId, result |-> result]);
            end if
            \* TODO if not from originator send a Error response? Only originator can request validity (final commit)
        end if
    else 
        lsom: sendMessage([from |-> to, to |-> from, type |-> "LiftValidResultJSON", liftId |-> liftId, result |-> lifts[arbitrator][liftId].state]);
    end if;
    lprintDecision: printLater(result);
    DLVR: return;
end procedure

procedure CheckLiftValidity(from, to, route, liftValue, originator, liftId, arbitrator)
    variables
        result,
begin
CkeckLiftValidity:
    printLater("Checking Lift Validity");
    if liftId \notin DOMAIN lifts[arbitrator] \/ (liftId \in DOMAIN lifts[arbitrator] /\ lifts[arbitrator][liftId].state = "Seek") then \* if not seen before or still seek make decision
        if \E lm \in lostMessages : lm.liftId = liftId then
            result := "Fail";
        else
            lchecktime: with validDecision \in {"Seek", "Fail"} do
                result := validDecision;
            end with;
        end if;
        lsr: lifts[arbitrator] := liftId :> [originator |-> originator, value |-> liftValue, state |-> result, route |-> route, arbitrator |-> arbitrator];
        lsm2: sendMessage([from |-> to, to |-> from, type |-> "LiftCheckResultJSON", liftId |-> liftId, result |-> result]);
    else \* if Good or Fail allready send results
        result := lifts[arbitrator][liftId].state;
        lsom: sendMessage([from |-> to, to |-> from, type |-> "LiftCheckResultJSON", liftId |-> liftId, result |-> result]);
    end if;
    lprintDecision: printLater(result);
    DLVR: return;
end procedure

procedure ReceiveLiftValidResult (to, liftId, result)
    variables
        prevPeer,
        timeout,
begin
ValidateLift:
        printLater("Receiving Lift Valid Response");
        prevPeer := NextElemIn(to, lifts[to][liftId].route);
        if result = "Fail" then
            lpt: printLater("Lift Invalid");
            \*lifts[to][liftId].state := "Fail";
            lsm1: sendMessage([liftId |-> liftId, from |-> to, to |-> prevPeer, type |-> "LiftFailJSON"]);
            L1: tallies[<<to, prevPeer, "Foil">>].projectedBalance := tallies[<<to, prevPeer, "Foil">>].projectedBalance - lifts[to][liftId].value;
        else
            if to = lifts[to][liftId].originator then
                lpv: printLater("Lift Valid");
                \*lifts[to][liftId].state := "Good";
                lsm: sendMessage([liftId |-> liftId, from |-> to, to |-> prevPeer, type |-> "LiftCommitJSON"]);
                L2: tallies[<<to, prevPeer, "Foil">>].balance := tallies[<<to, prevPeer, "Foil">>].balance + lifts[to][liftId].value;
            end if;
        end if;
        VLR: return;
end procedure

procedure ReceiveLiftCheckResult (to, liftId, result)
    variables
        prevPeer,
        timeout,
begin
ValidateLift:
        printLater("Receving Lift Check Response");
        prevPeer := NextElemIn(to, lifts[to][liftId].route);
        if result = "Fail" then
            lpt: printLater("Lift Invalid");
            call FailLift(to, prevPeer, liftId)
        end if;
        VLR: return;
end procedure

procedure CommitLift (from, to, liftId)
    variables
        nextPeer,
        liftValue,
begin
CommitLift:
	printLater("Commit Lift");
    liftValue := lifts[to][liftId].value;
    lifts[to][liftId].state := "Good";
    CL2: tallies[<<to, from, "Stock">>].balance := tallies[<<to, from, "Stock">>].balance - liftValue;
    if to /= lifts[to][liftId].originator then
        nextPeer := NextElemIn(to, lifts[to][liftId].route);
        CL4: sendMessage([liftId |-> liftId, from |-> to, to |-> nextPeer, type |-> "LiftCommitJSON"]);
        CL3: tallies[<<to, nextPeer, "Foil">>].balance := tallies[<<to, nextPeer, "Foil">>].balance + liftValue;
    end if;
    CLR: return;
end procedure

procedure FailLift (from, to, liftId)
    variables
        nextPeer,
        liftValue,
begin
FailLift:
	printLater("Fail Lift");
    if liftId \in DOMAIN lifts[to] then \* ignore lifts we haven't heard of before
        liftValue := lifts[to][liftId].value;
        lifts[to][liftId].state := "Fail";
        CL2: tallies[<<to, from, "Stock">>].projectedBalance := tallies[<<to, from, "Stock">>].projectedBalance + liftValue;
        if to /= lifts[to][liftId].originator then
            nextPeer := NextElemIn(to, lifts[to][liftId].route);
            CL4: sendMessage([liftId |-> liftId, from |-> to, to |-> nextPeer, type |-> "LiftFailJSON"]);
            CL3: tallies[<<to, nextPeer, "Foil">>].projectedBalance := tallies[<<to, nextPeer, "Foil">>].projectedBalance - liftValue;
        end if;
    end if;
    CLR: return;
end procedure

procedure CheckTimeout (from, liftId, arbitrator)
    variables
begin
CheckTimeout:
	printLater("Check Timeout");
    losm: sendMessage([liftId |-> liftId, originator |-> originator, from |-> from, to |-> arbitrator, type |-> "LiftCheckJSON", route |-> lifts[from][liftId].route, value |-> lifts[from][liftId].value, arbitrator |-> arbitrator]);
    CTR: return;
end procedure

fair process procId \in Users \* one process for each user
    variables
        cycle,
        liftValue,
        arbitrator,
        toAct,
        lostMes,
        printBuffer = <<>>,
begin
ProcStart:
    printLater("Start");
    l1: printLater(self);
    if self \in LiftProposers then
        cycle := CHOOSE c \in Cycles : c[1] = self; \* pick a cycle
        liftValue := MaxLiftValueFor(cycle, tallies);
        arbitrator := CHOOSE a \in ReliableUsers : TRUE;
        call ProposeLift(self, cycle, liftValue, arbitrator);
    end if;
    lsn: startedNodes := UNION{startedNodes, {self}};
    las: await startedNodes = Users; \* wait for the first message to pop in the bag
    l2w: while NotDone(lifts, Users, messages, UNION{readMessages, lostMessages}) do
    if (\E message \in messages: message \notin UNION{readMessages, lostMessages} /\ message.to = self) then
        if messages \ UNION{readMessages,lostMessages} /= {} then
            toAct := CHOOSE message \in messages: message \notin UNION{readMessages,lostMessages} /\ message.to = self;
            if toAct.type = "LiftProposeJSON" then
                call HandleLift(toAct.from, toAct.to, toAct.route, toAct.value, toAct.originator, toAct.liftId, toAct.arbitrator) ;
            end if;
            l5: if toAct.type = "LiftCommitJSON" then
                call CommitLift(toAct.from, toAct.to, toAct.liftId)
            end if;
            l6: if toAct.type = "LiftFailJSON" then
                call FailLift(toAct.from, toAct.to, toAct.liftId)
            end if;
            l7: if toAct.type = "LiftValidateJSON" then
                call DecideLiftValidity(toAct.from, toAct.to, toAct.route, toAct.value, toAct.originator, toAct.liftId, toAct.arbitrator)
            end if;
            l8: if toAct.type = "LiftCheckJSON" then
                call CheckLiftValidity(toAct.from, toAct.to, toAct.route, toAct.value, toAct.originator, toAct.liftId, toAct.arbitrator)
            end if;
            l9: if toAct.type = "LiftValidResultJSON" then
                call ReceiveLiftValidResult (toAct.to, toAct.liftId, toAct.result)
            end if;
            l10: if toAct.type = "LiftCheckResultJSON" then
                call ReceiveLiftCheckResult (toAct.to, toAct.liftId, toAct.result)
            end if;

            l4: readMessages := UNION{readMessages, {toAct}};
        end if;
    else
        if \E message \in lostMessages : message \notin readMessages /\ message.to = self then
        \* if a message to me was lost
            clm: lostMes := CHOOSE message \in lostMessages : message \notin readMessages /\ (message.to = self \/ message.from = self) ;
            lcl: if (lostMes.type = "LiftCommitJSON" \/ lostMes.type = "LiftFailJSON") /\ lostMes.to = self then
            \* will for sure check if the message was lost
                if lostMes.liftId \in DOMAIN lifts[self] /\ lifts[self][lostMes.liftId].arbitrator /= self /\ lifts[self][lostMes.liftId].state = "Seek" then
                    call CheckTimeout(self, lostMes.liftId, lifts[self][lostMes.liftId].arbitrator);
                end if;
            end if;
            lpl: if lostMes.type = "LiftProposeJSON" /\ lostMes.from = self then
            \* will for sure check if the message was lost
                if lostMes.liftId \in DOMAIN lifts[self] /\ lifts[self][lostMes.liftId].arbitrator /= self /\ lifts[self][lostMes.liftId].state = "Seek" then
                    call CheckTimeout(self, lostMes.liftId, lifts[self][lostMes.liftId].arbitrator);
                end if;
            end if;
            lrlmf: readMessages := UNION{readMessages, {lostMes}};

        (*
        else
        with lid \in UNION{{0}, {lid \in DOMAIN lifts[self] : lifts[self][lid].arbitrator /= self /\ lifts[self][lid].state = "Seek"}} do
            printLater(lid);
            if lid /= 0 then \* if 0 don't check
                call CheckTimeout(self, lid, lifts[self][lid].arbitrator);
            end if
        end with;
        *)
        end if;
    end if;
    end while;
    (*print readMessages;
    print lifts;
    print tallies;
    *)
    lpb: print printBuffer
end process


end algorithm *)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-a2ef078ae9eafa2148ca70c7614ae376
\* Label ProposeLift of procedure ProposeLift at line 66 col 5 changed to ProposeLift_
\* Label lsm of procedure ProposeLift at line 70 col 5 changed to lsm_
\* Label HandleLift of procedure HandleLift at line 66 col 5 changed to HandleLift_
\* Label L1 of procedure HandleLift at line 112 col 13 changed to L1_
\* Label lsm of procedure HandleLift at line 70 col 5 changed to lsm_H
\* Label losm of procedure HandleLift at line 70 col 5 changed to losm_
\* Label DecideLiftValidity of procedure DecideLiftValidity at line 66 col 5 changed to DecideLiftValidity_
\* Label lchecktime of procedure DecideLiftValidity at line 129 col 25 changed to lchecktime_
\* Label lsm of procedure DecideLiftValidity at line 70 col 5 changed to lsm_D
\* Label lsom of procedure DecideLiftValidity at line 70 col 5 changed to lsom_
\* Label lprintDecision of procedure DecideLiftValidity at line 66 col 5 changed to lprintDecision_
\* Label DLVR of procedure DecideLiftValidity at line 142 col 11 changed to DLVR_
\* Label ValidateLift of procedure ReceiveLiftValidResult at line 66 col 5 changed to ValidateLift_
\* Label lpt of procedure ReceiveLiftValidResult at line 66 col 5 changed to lpt_
\* Label VLR of procedure ReceiveLiftValidResult at line 190 col 14 changed to VLR_
\* Label CommitLift of procedure CommitLift at line 66 col 5 changed to CommitLift_
\* Label CL2 of procedure CommitLift at line 217 col 10 changed to CL2_
\* Label CL4 of procedure CommitLift at line 70 col 5 changed to CL4_
\* Label CL3 of procedure CommitLift at line 221 col 14 changed to CL3_
\* Label CLR of procedure CommitLift at line 223 col 10 changed to CLR_
\* Label FailLift of procedure FailLift at line 66 col 5 changed to FailLift_
\* Label CheckTimeout of procedure CheckTimeout at line 66 col 5 changed to CheckTimeout_
\* Process variable cycle of process procId at line 257 col 9 changed to cycle_
\* Process variable liftValue of process procId at line 258 col 9 changed to liftValue_
\* Process variable arbitrator of process procId at line 259 col 9 changed to arbitrator_
\* Procedure variable nextPeer of procedure ProposeLift at line 88 col 9 changed to nextPeer_
\* Procedure variable prevPeer of procedure HandleLift at line 104 col 9 changed to prevPeer_
\* Procedure variable result of procedure DecideLiftValidity at line 123 col 9 changed to result_
\* Procedure variable result of procedure CheckLiftValidity at line 147 col 9 changed to result_C
\* Procedure variable prevPeer of procedure ReceiveLiftValidResult at line 171 col 9 changed to prevPeer_R
\* Procedure variable timeout of procedure ReceiveLiftValidResult at line 172 col 9 changed to timeout_
\* Procedure variable nextPeer of procedure CommitLift at line 210 col 9 changed to nextPeer_C
\* Procedure variable liftValue of procedure CommitLift at line 211 col 9 changed to liftValue_C
\* Procedure variable liftValue of procedure FailLift at line 229 col 9 changed to liftValue_F
\* Parameter liftValue of procedure ProposeLift at line 86 col 41 changed to liftValue_P
\* Parameter arbitrator of procedure ProposeLift at line 86 col 52 changed to arbitrator_P
\* Parameter from of procedure HandleLift at line 102 col 23 changed to from_
\* Parameter to of procedure HandleLift at line 102 col 29 changed to to_
\* Parameter route of procedure HandleLift at line 102 col 33 changed to route_
\* Parameter liftValue of procedure HandleLift at line 102 col 40 changed to liftValue_H
\* Parameter originator of procedure HandleLift at line 102 col 51 changed to originator_
\* Parameter liftId of procedure HandleLift at line 102 col 63 changed to liftId_
\* Parameter arbitrator of procedure HandleLift at line 102 col 71 changed to arbitrator_H
\* Parameter from of procedure DecideLiftValidity at line 121 col 30 changed to from_D
\* Parameter to of procedure DecideLiftValidity at line 121 col 36 changed to to_D
\* Parameter route of procedure DecideLiftValidity at line 121 col 40 changed to route_D
\* Parameter liftValue of procedure DecideLiftValidity at line 121 col 47 changed to liftValue_D
\* Parameter originator of procedure DecideLiftValidity at line 121 col 58 changed to originator_D
\* Parameter liftId of procedure DecideLiftValidity at line 121 col 70 changed to liftId_D
\* Parameter arbitrator of procedure DecideLiftValidity at line 121 col 78 changed to arbitrator_D
\* Parameter from of procedure CheckLiftValidity at line 145 col 29 changed to from_C
\* Parameter to of procedure CheckLiftValidity at line 145 col 35 changed to to_C
\* Parameter liftId of procedure CheckLiftValidity at line 145 col 69 changed to liftId_C
\* Parameter arbitrator of procedure CheckLiftValidity at line 145 col 77 changed to arbitrator_C
\* Parameter to of procedure ReceiveLiftValidResult at line 169 col 35 changed to to_R
\* Parameter liftId of procedure ReceiveLiftValidResult at line 169 col 39 changed to liftId_R
\* Parameter result of procedure ReceiveLiftValidResult at line 169 col 47 changed to result_R
\* Parameter to of procedure ReceiveLiftCheckResult at line 193 col 35 changed to to_Re
\* Parameter liftId of procedure ReceiveLiftCheckResult at line 193 col 39 changed to liftId_Re
\* Parameter from of procedure CommitLift at line 208 col 23 changed to from_Co
\* Parameter to of procedure CommitLift at line 208 col 29 changed to to_Co
\* Parameter liftId of procedure CommitLift at line 208 col 33 changed to liftId_Co
\* Parameter from of procedure FailLift at line 226 col 21 changed to from_F
\* Parameter liftId of procedure FailLift at line 226 col 31 changed to liftId_F
CONSTANT defaultInitValue
VARIABLES Users, LiftProposers, ReliableUsers, Links, Cycles, tallies, 
          messages, readMessages, lostMessages, lifts, startedNodes, 
          nextLiftGuid, pc, stack, proposer, cycle, liftValue_P, arbitrator_P, 
          nextPeer_, liftGuid, from_, to_, route_, liftValue_H, originator_, 
          liftId_, arbitrator_H, prevPeer_, from_D, to_D, route_D, 
          liftValue_D, originator_D, liftId_D, arbitrator_D, result_, from_C, 
          to_C, route, liftValue, originator, liftId_C, arbitrator_C, 
          result_C, to_R, liftId_R, result_R, prevPeer_R, timeout_, to_Re, 
          liftId_Re, result, prevPeer, timeout, from_Co, to_Co, liftId_Co, 
          nextPeer_C, liftValue_C, from_F, to, liftId_F, nextPeer, 
          liftValue_F, from, liftId, arbitrator, cycle_, liftValue_, 
          arbitrator_, toAct, lostMes, printBuffer

vars == << Users, LiftProposers, ReliableUsers, Links, Cycles, tallies, 
           messages, readMessages, lostMessages, lifts, startedNodes, 
           nextLiftGuid, pc, stack, proposer, cycle, liftValue_P, 
           arbitrator_P, nextPeer_, liftGuid, from_, to_, route_, liftValue_H, 
           originator_, liftId_, arbitrator_H, prevPeer_, from_D, to_D, 
           route_D, liftValue_D, originator_D, liftId_D, arbitrator_D, 
           result_, from_C, to_C, route, liftValue, originator, liftId_C, 
           arbitrator_C, result_C, to_R, liftId_R, result_R, prevPeer_R, 
           timeout_, to_Re, liftId_Re, result, prevPeer, timeout, from_Co, 
           to_Co, liftId_Co, nextPeer_C, liftValue_C, from_F, to, liftId_F, 
           nextPeer, liftValue_F, from, liftId, arbitrator, cycle_, 
           liftValue_, arbitrator_, toAct, lostMes, printBuffer >>

ProcSet == (Users)

Init == (* Global variables *)
        /\ Users = {A, B, C, D}
        /\ LiftProposers = {A}
        /\ ReliableUsers = {D}
        /\ Links = {<<A, B>>, <<B, C>>, <<C, D>>, <<C, A>>, <<D, A>>}
        /\ Cycles = {<<A, B, C>>}
        /\ tallies = [id \in UNION{{<<x, y, "Foil">>, <<y, x, "Stock">>}: <<x, y>> \in Links} |-> [balance |-> InitTallyBalance(id), projectedBalance |-> InitTallyProjBalance(id) ]]
        /\ messages = {}
        /\ readMessages = {}
        /\ lostMessages = {}
        /\ lifts = [user \in Users |-> [id \in {} |-> 0]]
        /\ startedNodes = {}
        /\ nextLiftGuid = 1
        (* Procedure ProposeLift *)
        /\ proposer = [ self \in ProcSet |-> defaultInitValue]
        /\ cycle = [ self \in ProcSet |-> defaultInitValue]
        /\ liftValue_P = [ self \in ProcSet |-> defaultInitValue]
        /\ arbitrator_P = [ self \in ProcSet |-> defaultInitValue]
        /\ nextPeer_ = [ self \in ProcSet |-> defaultInitValue]
        /\ liftGuid = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure HandleLift *)
        /\ from_ = [ self \in ProcSet |-> defaultInitValue]
        /\ to_ = [ self \in ProcSet |-> defaultInitValue]
        /\ route_ = [ self \in ProcSet |-> defaultInitValue]
        /\ liftValue_H = [ self \in ProcSet |-> defaultInitValue]
        /\ originator_ = [ self \in ProcSet |-> defaultInitValue]
        /\ liftId_ = [ self \in ProcSet |-> defaultInitValue]
        /\ arbitrator_H = [ self \in ProcSet |-> defaultInitValue]
        /\ prevPeer_ = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure DecideLiftValidity *)
        /\ from_D = [ self \in ProcSet |-> defaultInitValue]
        /\ to_D = [ self \in ProcSet |-> defaultInitValue]
        /\ route_D = [ self \in ProcSet |-> defaultInitValue]
        /\ liftValue_D = [ self \in ProcSet |-> defaultInitValue]
        /\ originator_D = [ self \in ProcSet |-> defaultInitValue]
        /\ liftId_D = [ self \in ProcSet |-> defaultInitValue]
        /\ arbitrator_D = [ self \in ProcSet |-> defaultInitValue]
        /\ result_ = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure CheckLiftValidity *)
        /\ from_C = [ self \in ProcSet |-> defaultInitValue]
        /\ to_C = [ self \in ProcSet |-> defaultInitValue]
        /\ route = [ self \in ProcSet |-> defaultInitValue]
        /\ liftValue = [ self \in ProcSet |-> defaultInitValue]
        /\ originator = [ self \in ProcSet |-> defaultInitValue]
        /\ liftId_C = [ self \in ProcSet |-> defaultInitValue]
        /\ arbitrator_C = [ self \in ProcSet |-> defaultInitValue]
        /\ result_C = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure ReceiveLiftValidResult *)
        /\ to_R = [ self \in ProcSet |-> defaultInitValue]
        /\ liftId_R = [ self \in ProcSet |-> defaultInitValue]
        /\ result_R = [ self \in ProcSet |-> defaultInitValue]
        /\ prevPeer_R = [ self \in ProcSet |-> defaultInitValue]
        /\ timeout_ = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure ReceiveLiftCheckResult *)
        /\ to_Re = [ self \in ProcSet |-> defaultInitValue]
        /\ liftId_Re = [ self \in ProcSet |-> defaultInitValue]
        /\ result = [ self \in ProcSet |-> defaultInitValue]
        /\ prevPeer = [ self \in ProcSet |-> defaultInitValue]
        /\ timeout = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure CommitLift *)
        /\ from_Co = [ self \in ProcSet |-> defaultInitValue]
        /\ to_Co = [ self \in ProcSet |-> defaultInitValue]
        /\ liftId_Co = [ self \in ProcSet |-> defaultInitValue]
        /\ nextPeer_C = [ self \in ProcSet |-> defaultInitValue]
        /\ liftValue_C = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure FailLift *)
        /\ from_F = [ self \in ProcSet |-> defaultInitValue]
        /\ to = [ self \in ProcSet |-> defaultInitValue]
        /\ liftId_F = [ self \in ProcSet |-> defaultInitValue]
        /\ nextPeer = [ self \in ProcSet |-> defaultInitValue]
        /\ liftValue_F = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure CheckTimeout *)
        /\ from = [ self \in ProcSet |-> defaultInitValue]
        /\ liftId = [ self \in ProcSet |-> defaultInitValue]
        /\ arbitrator = [ self \in ProcSet |-> defaultInitValue]
        (* Process procId *)
        /\ cycle_ = [self \in Users |-> defaultInitValue]
        /\ liftValue_ = [self \in Users |-> defaultInitValue]
        /\ arbitrator_ = [self \in Users |-> defaultInitValue]
        /\ toAct = [self \in Users |-> defaultInitValue]
        /\ lostMes = [self \in Users |-> defaultInitValue]
        /\ printBuffer = [self \in Users |-> <<>>]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "ProcStart"]

ProposeLift_(self) == /\ pc[self] = "ProposeLift_"
                      /\ printBuffer' = [printBuffer EXCEPT ![self] = Append(printBuffer[self], "Proposing Lift")]
                      /\ prevPeer' = [prevPeer EXCEPT ![self] = PrevElemIn(proposer[self], cycle[self])]
                      /\ liftGuid' = [liftGuid EXCEPT ![self] = nextLiftGuid]
                      /\ nextLiftGuid' = nextLiftGuid + 1
                      /\ lifts' = [lifts EXCEPT ![proposer[self]] = liftGuid'[self] :> [originator |-> proposer[self], value |-> liftValue_P[self], state |-> "Seek", route |-> cycle[self], arbitrator |-> arbitrator_P[self]]]
                      /\ tallies' = [tallies EXCEPT ![<<proposer[self], prevPeer'[self], "Stock">>].projectedBalance = tallies[<<proposer[self], prevPeer'[self], "Stock">>].projectedBalance - liftValue_P[self]]
                      /\ pc' = [pc EXCEPT ![self] = "lsm_"]
                      /\ UNCHANGED << Users, LiftProposers, ReliableUsers, 
                                      Links, Cycles, messages, readMessages, 
                                      lostMessages, startedNodes, stack, 
                                      proposer, cycle, liftValue_P, 
                                      arbitrator_P, nextPeer_, from_, to_, 
                                      route_, liftValue_H, originator_, 
                                      liftId_, arbitrator_H, prevPeer_, from_D, 
                                      to_D, route_D, liftValue_D, originator_D, 
                                      liftId_D, arbitrator_D, result_, from_C, 
                                      to_C, route, liftValue, originator, 
                                      liftId_C, arbitrator_C, result_C, to_R, 
                                      liftId_R, result_R, prevPeer_R, timeout_, 
                                      to_Re, liftId_Re, result, timeout, 
                                      from_Co, to_Co, liftId_Co, nextPeer_C, 
                                      liftValue_C, from_F, to, liftId_F, 
                                      nextPeer, liftValue_F, from, liftId, 
                                      arbitrator, cycle_, liftValue_, 
                                      arbitrator_, toAct, lostMes >>

lsm_(self) == /\ pc[self] = "lsm_"
              /\ IF MESSAGES_FAIL
                    THEN /\ \E messageWorks \in {TRUE, FALSE}:
                              IF messageWorks \/ ([liftId |-> liftGuid[self], originator |-> proposer[self], from |-> proposer[self], to |-> prevPeer[self], type |-> "LiftProposeJSON", route |-> cycle[self], value |-> liftValue_P[self], arbitrator |-> arbitrator_P[self]]).to \in ReliableUsers \/ ([liftId |-> liftGuid[self], originator |-> proposer[self], from |-> proposer[self], to |-> prevPeer[self], type |-> "LiftProposeJSON", route |-> cycle[self], value |-> liftValue_P[self], arbitrator |-> arbitrator_P[self]]).from \in ReliableUsers
                                 THEN /\ messages' = UNION{messages, {([liftId |-> liftGuid[self], originator |-> proposer[self], from |-> proposer[self], to |-> prevPeer[self], type |-> "LiftProposeJSON", route |-> cycle[self], value |-> liftValue_P[self], arbitrator |-> arbitrator_P[self]])}}
                                      /\ UNCHANGED << lostMessages, 
                                                      printBuffer >>
                                 ELSE /\ printBuffer' = [printBuffer EXCEPT ![self] = Append(printBuffer[self], "Message Failed")]
                                      /\ messages' = UNION{messages, {([liftId |-> liftGuid[self], originator |-> proposer[self], from |-> proposer[self], to |-> prevPeer[self], type |-> "LiftProposeJSON", route |-> cycle[self], value |-> liftValue_P[self], arbitrator |-> arbitrator_P[self]])}}
                                      /\ lostMessages' = UNION{lostMessages, {([liftId |-> liftGuid[self], originator |-> proposer[self], from |-> proposer[self], to |-> prevPeer[self], type |-> "LiftProposeJSON", route |-> cycle[self], value |-> liftValue_P[self], arbitrator |-> arbitrator_P[self]])}}
                    ELSE /\ messages' = UNION{messages, {([liftId |-> liftGuid[self], originator |-> proposer[self], from |-> proposer[self], to |-> prevPeer[self], type |-> "LiftProposeJSON", route |-> cycle[self], value |-> liftValue_P[self], arbitrator |-> arbitrator_P[self]])}}
                         /\ UNCHANGED << lostMessages, printBuffer >>
              /\ pc' = [pc EXCEPT ![self] = "PLR"]
              /\ UNCHANGED << Users, LiftProposers, ReliableUsers, Links, 
                              Cycles, tallies, readMessages, lifts, 
                              startedNodes, nextLiftGuid, stack, proposer, 
                              cycle, liftValue_P, arbitrator_P, nextPeer_, 
                              liftGuid, from_, to_, route_, liftValue_H, 
                              originator_, liftId_, arbitrator_H, prevPeer_, 
                              from_D, to_D, route_D, liftValue_D, originator_D, 
                              liftId_D, arbitrator_D, result_, from_C, to_C, 
                              route, liftValue, originator, liftId_C, 
                              arbitrator_C, result_C, to_R, liftId_R, result_R, 
                              prevPeer_R, timeout_, to_Re, liftId_Re, result, 
                              prevPeer, timeout, from_Co, to_Co, liftId_Co, 
                              nextPeer_C, liftValue_C, from_F, to, liftId_F, 
                              nextPeer, liftValue_F, from, liftId, arbitrator, 
                              cycle_, liftValue_, arbitrator_, toAct, lostMes >>

PLR(self) == /\ pc[self] = "PLR"
             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
             /\ nextPeer_' = [nextPeer_ EXCEPT ![self] = Head(stack[self]).nextPeer_]
             /\ liftGuid' = [liftGuid EXCEPT ![self] = Head(stack[self]).liftGuid]
             /\ proposer' = [proposer EXCEPT ![self] = Head(stack[self]).proposer]
             /\ cycle' = [cycle EXCEPT ![self] = Head(stack[self]).cycle]
             /\ liftValue_P' = [liftValue_P EXCEPT ![self] = Head(stack[self]).liftValue_P]
             /\ arbitrator_P' = [arbitrator_P EXCEPT ![self] = Head(stack[self]).arbitrator_P]
             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
             /\ UNCHANGED << Users, LiftProposers, ReliableUsers, Links, 
                             Cycles, tallies, messages, readMessages, 
                             lostMessages, lifts, startedNodes, nextLiftGuid, 
                             from_, to_, route_, liftValue_H, originator_, 
                             liftId_, arbitrator_H, prevPeer_, from_D, to_D, 
                             route_D, liftValue_D, originator_D, liftId_D, 
                             arbitrator_D, result_, from_C, to_C, route, 
                             liftValue, originator, liftId_C, arbitrator_C, 
                             result_C, to_R, liftId_R, result_R, prevPeer_R, 
                             timeout_, to_Re, liftId_Re, result, prevPeer, 
                             timeout, from_Co, to_Co, liftId_Co, nextPeer_C, 
                             liftValue_C, from_F, to, liftId_F, nextPeer, 
                             liftValue_F, from, liftId, arbitrator, cycle_, 
                             liftValue_, arbitrator_, toAct, lostMes, 
                             printBuffer >>

ProposeLift(self) == ProposeLift_(self) \/ lsm_(self) \/ PLR(self)

HandleLift_(self) == /\ pc[self] = "HandleLift_"
                     /\ printBuffer' = [printBuffer EXCEPT ![self] = Append(printBuffer[self], "Handling Lift")]
                     /\ prevPeer_' = [prevPeer_ EXCEPT ![self] = PrevElemIn(to_[self], route_[self])]
                     /\ lifts' = [lifts EXCEPT ![to_[self]] = liftId_[self] :> [originator |-> originator_[self], value |-> liftValue_H[self], state |-> "Seek", route |-> route_[self], arbitrator |-> arbitrator_H[self]]]
                     /\ tallies' = [tallies EXCEPT ![<<to_[self], from_[self], "Foil">>].projectedBalance = tallies[<<to_[self], from_[self], "Foil">>].projectedBalance + liftValue_H[self]]
                     /\ IF to_[self] /= originator_[self]
                           THEN /\ pc' = [pc EXCEPT ![self] = "L1_"]
                           ELSE /\ pc' = [pc EXCEPT ![self] = "losm_"]
                     /\ UNCHANGED << Users, LiftProposers, ReliableUsers, 
                                     Links, Cycles, messages, readMessages, 
                                     lostMessages, startedNodes, nextLiftGuid, 
                                     stack, proposer, cycle, liftValue_P, 
                                     arbitrator_P, nextPeer_, liftGuid, from_, 
                                     to_, route_, liftValue_H, originator_, 
                                     liftId_, arbitrator_H, from_D, to_D, 
                                     route_D, liftValue_D, originator_D, 
                                     liftId_D, arbitrator_D, result_, from_C, 
                                     to_C, route, liftValue, originator, 
                                     liftId_C, arbitrator_C, result_C, to_R, 
                                     liftId_R, result_R, prevPeer_R, timeout_, 
                                     to_Re, liftId_Re, result, prevPeer, 
                                     timeout, from_Co, to_Co, liftId_Co, 
                                     nextPeer_C, liftValue_C, from_F, to, 
                                     liftId_F, nextPeer, liftValue_F, from, 
                                     liftId, arbitrator, cycle_, liftValue_, 
                                     arbitrator_, toAct, lostMes >>

L1_(self) == /\ pc[self] = "L1_"
             /\ tallies' = [tallies EXCEPT ![<<to_[self], prevPeer_[self], "Stock">>].projectedBalance = tallies[<<to_[self], prevPeer_[self], "Stock">>].projectedBalance - liftValue_H[self]]
             /\ pc' = [pc EXCEPT ![self] = "lsm_H"]
             /\ UNCHANGED << Users, LiftProposers, ReliableUsers, Links, 
                             Cycles, messages, readMessages, lostMessages, 
                             lifts, startedNodes, nextLiftGuid, stack, 
                             proposer, cycle, liftValue_P, arbitrator_P, 
                             nextPeer_, liftGuid, from_, to_, route_, 
                             liftValue_H, originator_, liftId_, arbitrator_H, 
                             prevPeer_, from_D, to_D, route_D, liftValue_D, 
                             originator_D, liftId_D, arbitrator_D, result_, 
                             from_C, to_C, route, liftValue, originator, 
                             liftId_C, arbitrator_C, result_C, to_R, liftId_R, 
                             result_R, prevPeer_R, timeout_, to_Re, liftId_Re, 
                             result, prevPeer, timeout, from_Co, to_Co, 
                             liftId_Co, nextPeer_C, liftValue_C, from_F, to, 
                             liftId_F, nextPeer, liftValue_F, from, liftId, 
                             arbitrator, cycle_, liftValue_, arbitrator_, 
                             toAct, lostMes, printBuffer >>

lsm_H(self) == /\ pc[self] = "lsm_H"
               /\ IF MESSAGES_FAIL
                     THEN /\ \E messageWorks \in {TRUE, FALSE}:
                               IF messageWorks \/ ([liftId |-> liftId_[self], originator |-> originator_[self], from |-> to_[self], to |-> prevPeer_[self], type |-> "LiftProposeJSON", route |-> route_[self], value |-> liftValue_H[self], arbitrator |-> arbitrator_H[self]]).to \in ReliableUsers \/ ([liftId |-> liftId_[self], originator |-> originator_[self], from |-> to_[self], to |-> prevPeer_[self], type |-> "LiftProposeJSON", route |-> route_[self], value |-> liftValue_H[self], arbitrator |-> arbitrator_H[self]]).from \in ReliableUsers
                                  THEN /\ messages' = UNION{messages, {([liftId |-> liftId_[self], originator |-> originator_[self], from |-> to_[self], to |-> prevPeer_[self], type |-> "LiftProposeJSON", route |-> route_[self], value |-> liftValue_H[self], arbitrator |-> arbitrator_H[self]])}}
                                       /\ UNCHANGED << lostMessages, 
                                                       printBuffer >>
                                  ELSE /\ printBuffer' = [printBuffer EXCEPT ![self] = Append(printBuffer[self], "Message Failed")]
                                       /\ messages' = UNION{messages, {([liftId |-> liftId_[self], originator |-> originator_[self], from |-> to_[self], to |-> prevPeer_[self], type |-> "LiftProposeJSON", route |-> route_[self], value |-> liftValue_H[self], arbitrator |-> arbitrator_H[self]])}}
                                       /\ lostMessages' = UNION{lostMessages, {([liftId |-> liftId_[self], originator |-> originator_[self], from |-> to_[self], to |-> prevPeer_[self], type |-> "LiftProposeJSON", route |-> route_[self], value |-> liftValue_H[self], arbitrator |-> arbitrator_H[self]])}}
                     ELSE /\ messages' = UNION{messages, {([liftId |-> liftId_[self], originator |-> originator_[self], from |-> to_[self], to |-> prevPeer_[self], type |-> "LiftProposeJSON", route |-> route_[self], value |-> liftValue_H[self], arbitrator |-> arbitrator_H[self]])}}
                          /\ UNCHANGED << lostMessages, printBuffer >>
               /\ pc' = [pc EXCEPT ![self] = "HLR"]
               /\ UNCHANGED << Users, LiftProposers, ReliableUsers, Links, 
                               Cycles, tallies, readMessages, lifts, 
                               startedNodes, nextLiftGuid, stack, proposer, 
                               cycle, liftValue_P, arbitrator_P, nextPeer_, 
                               liftGuid, from_, to_, route_, liftValue_H, 
                               originator_, liftId_, arbitrator_H, prevPeer_, 
                               from_D, to_D, route_D, liftValue_D, 
                               originator_D, liftId_D, arbitrator_D, result_, 
                               from_C, to_C, route, liftValue, originator, 
                               liftId_C, arbitrator_C, result_C, to_R, 
                               liftId_R, result_R, prevPeer_R, timeout_, to_Re, 
                               liftId_Re, result, prevPeer, timeout, from_Co, 
                               to_Co, liftId_Co, nextPeer_C, liftValue_C, 
                               from_F, to, liftId_F, nextPeer, liftValue_F, 
                               from, liftId, arbitrator, cycle_, liftValue_, 
                               arbitrator_, toAct, lostMes >>

losm_(self) == /\ pc[self] = "losm_"
               /\ IF MESSAGES_FAIL
                     THEN /\ \E messageWorks \in {TRUE, FALSE}:
                               IF messageWorks \/ ([liftId |-> liftId_[self], originator |-> originator_[self], from |-> to_[self], to |-> arbitrator_H[self], type |-> "LiftValidateJSON", route |-> route_[self], value |-> liftValue_H[self], arbitrator |-> arbitrator_H[self]]).to \in ReliableUsers \/ ([liftId |-> liftId_[self], originator |-> originator_[self], from |-> to_[self], to |-> arbitrator_H[self], type |-> "LiftValidateJSON", route |-> route_[self], value |-> liftValue_H[self], arbitrator |-> arbitrator_H[self]]).from \in ReliableUsers
                                  THEN /\ messages' = UNION{messages, {([liftId |-> liftId_[self], originator |-> originator_[self], from |-> to_[self], to |-> arbitrator_H[self], type |-> "LiftValidateJSON", route |-> route_[self], value |-> liftValue_H[self], arbitrator |-> arbitrator_H[self]])}}
                                       /\ UNCHANGED << lostMessages, 
                                                       printBuffer >>
                                  ELSE /\ printBuffer' = [printBuffer EXCEPT ![self] = Append(printBuffer[self], "Message Failed")]
                                       /\ messages' = UNION{messages, {([liftId |-> liftId_[self], originator |-> originator_[self], from |-> to_[self], to |-> arbitrator_H[self], type |-> "LiftValidateJSON", route |-> route_[self], value |-> liftValue_H[self], arbitrator |-> arbitrator_H[self]])}}
                                       /\ lostMessages' = UNION{lostMessages, {([liftId |-> liftId_[self], originator |-> originator_[self], from |-> to_[self], to |-> arbitrator_H[self], type |-> "LiftValidateJSON", route |-> route_[self], value |-> liftValue_H[self], arbitrator |-> arbitrator_H[self]])}}
                     ELSE /\ messages' = UNION{messages, {([liftId |-> liftId_[self], originator |-> originator_[self], from |-> to_[self], to |-> arbitrator_H[self], type |-> "LiftValidateJSON", route |-> route_[self], value |-> liftValue_H[self], arbitrator |-> arbitrator_H[self]])}}
                          /\ UNCHANGED << lostMessages, printBuffer >>
               /\ pc' = [pc EXCEPT ![self] = "HLR"]
               /\ UNCHANGED << Users, LiftProposers, ReliableUsers, Links, 
                               Cycles, tallies, readMessages, lifts, 
                               startedNodes, nextLiftGuid, stack, proposer, 
                               cycle, liftValue_P, arbitrator_P, nextPeer_, 
                               liftGuid, from_, to_, route_, liftValue_H, 
                               originator_, liftId_, arbitrator_H, prevPeer_, 
                               from_D, to_D, route_D, liftValue_D, 
                               originator_D, liftId_D, arbitrator_D, result_, 
                               from_C, to_C, route, liftValue, originator, 
                               liftId_C, arbitrator_C, result_C, to_R, 
                               liftId_R, result_R, prevPeer_R, timeout_, to_Re, 
                               liftId_Re, result, prevPeer, timeout, from_Co, 
                               to_Co, liftId_Co, nextPeer_C, liftValue_C, 
                               from_F, to, liftId_F, nextPeer, liftValue_F, 
                               from, liftId, arbitrator, cycle_, liftValue_, 
                               arbitrator_, toAct, lostMes >>

HLR(self) == /\ pc[self] = "HLR"
             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
             /\ prevPeer_' = [prevPeer_ EXCEPT ![self] = Head(stack[self]).prevPeer_]
             /\ from_' = [from_ EXCEPT ![self] = Head(stack[self]).from_]
             /\ to_' = [to_ EXCEPT ![self] = Head(stack[self]).to_]
             /\ route_' = [route_ EXCEPT ![self] = Head(stack[self]).route_]
             /\ liftValue_H' = [liftValue_H EXCEPT ![self] = Head(stack[self]).liftValue_H]
             /\ originator_' = [originator_ EXCEPT ![self] = Head(stack[self]).originator_]
             /\ liftId_' = [liftId_ EXCEPT ![self] = Head(stack[self]).liftId_]
             /\ arbitrator_H' = [arbitrator_H EXCEPT ![self] = Head(stack[self]).arbitrator_H]
             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
             /\ UNCHANGED << Users, LiftProposers, ReliableUsers, Links, 
                             Cycles, tallies, messages, readMessages, 
                             lostMessages, lifts, startedNodes, nextLiftGuid, 
                             proposer, cycle, liftValue_P, arbitrator_P, 
                             nextPeer_, liftGuid, from_D, to_D, route_D, 
                             liftValue_D, originator_D, liftId_D, arbitrator_D, 
                             result_, from_C, to_C, route, liftValue, 
                             originator, liftId_C, arbitrator_C, result_C, 
                             to_R, liftId_R, result_R, prevPeer_R, timeout_, 
                             to_Re, liftId_Re, result, prevPeer, timeout, 
                             from_Co, to_Co, liftId_Co, nextPeer_C, 
                             liftValue_C, from_F, to, liftId_F, nextPeer, 
                             liftValue_F, from, liftId, arbitrator, cycle_, 
                             liftValue_, arbitrator_, toAct, lostMes, 
                             printBuffer >>

HandleLift(self) == HandleLift_(self) \/ L1_(self) \/ lsm_H(self)
                       \/ losm_(self) \/ HLR(self)

DecideLiftValidity_(self) == /\ pc[self] = "DecideLiftValidity_"
                             /\ printBuffer' = [printBuffer EXCEPT ![self] = Append(printBuffer[self], "Deciding Lift Validity")]
                             /\ IF liftId_D[self] \notin DOMAIN lifts[arbitrator_D[self]] \/ (liftId_D[self] \in DOMAIN lifts[arbitrator_D[self]] /\ lifts[arbitrator_D[self]][liftId_D[self]].state = "Seek")
                                   THEN /\ IF to_D[self] = arbitrator_D[self]
                                              THEN /\ pc' = [pc EXCEPT ![self] = "lchecktime_"]
                                              ELSE /\ pc' = [pc EXCEPT ![self] = "lprintDecision_"]
                                   ELSE /\ pc' = [pc EXCEPT ![self] = "lsom_"]
                             /\ UNCHANGED << Users, LiftProposers, 
                                             ReliableUsers, Links, Cycles, 
                                             tallies, messages, readMessages, 
                                             lostMessages, lifts, startedNodes, 
                                             nextLiftGuid, stack, proposer, 
                                             cycle, liftValue_P, arbitrator_P, 
                                             nextPeer_, liftGuid, from_, to_, 
                                             route_, liftValue_H, originator_, 
                                             liftId_, arbitrator_H, prevPeer_, 
                                             from_D, to_D, route_D, 
                                             liftValue_D, originator_D, 
                                             liftId_D, arbitrator_D, result_, 
                                             from_C, to_C, route, liftValue, 
                                             originator, liftId_C, 
                                             arbitrator_C, result_C, to_R, 
                                             liftId_R, result_R, prevPeer_R, 
                                             timeout_, to_Re, liftId_Re, 
                                             result, prevPeer, timeout, 
                                             from_Co, to_Co, liftId_Co, 
                                             nextPeer_C, liftValue_C, from_F, 
                                             to, liftId_F, nextPeer, 
                                             liftValue_F, from, liftId, 
                                             arbitrator, cycle_, liftValue_, 
                                             arbitrator_, toAct, lostMes >>

lsom_(self) == /\ pc[self] = "lsom_"
               /\ IF MESSAGES_FAIL
                     THEN /\ \E messageWorks \in {TRUE, FALSE}:
                               IF messageWorks \/ ([from |-> to_D[self], to |-> from_D[self], type |-> "LiftValidResultJSON", liftId |-> liftId_D[self], result |-> lifts[arbitrator_D[self]][liftId_D[self]].state]).to \in ReliableUsers \/ ([from |-> to_D[self], to |-> from_D[self], type |-> "LiftValidResultJSON", liftId |-> liftId_D[self], result |-> lifts[arbitrator_D[self]][liftId_D[self]].state]).from \in ReliableUsers
                                  THEN /\ messages' = UNION{messages, {([from |-> to_D[self], to |-> from_D[self], type |-> "LiftValidResultJSON", liftId |-> liftId_D[self], result |-> lifts[arbitrator_D[self]][liftId_D[self]].state])}}
                                       /\ UNCHANGED << lostMessages, 
                                                       printBuffer >>
                                  ELSE /\ printBuffer' = [printBuffer EXCEPT ![self] = Append(printBuffer[self], "Message Failed")]
                                       /\ messages' = UNION{messages, {([from |-> to_D[self], to |-> from_D[self], type |-> "LiftValidResultJSON", liftId |-> liftId_D[self], result |-> lifts[arbitrator_D[self]][liftId_D[self]].state])}}
                                       /\ lostMessages' = UNION{lostMessages, {([from |-> to_D[self], to |-> from_D[self], type |-> "LiftValidResultJSON", liftId |-> liftId_D[self], result |-> lifts[arbitrator_D[self]][liftId_D[self]].state])}}
                     ELSE /\ messages' = UNION{messages, {([from |-> to_D[self], to |-> from_D[self], type |-> "LiftValidResultJSON", liftId |-> liftId_D[self], result |-> lifts[arbitrator_D[self]][liftId_D[self]].state])}}
                          /\ UNCHANGED << lostMessages, printBuffer >>
               /\ pc' = [pc EXCEPT ![self] = "lprintDecision_"]
               /\ UNCHANGED << Users, LiftProposers, ReliableUsers, Links, 
                               Cycles, tallies, readMessages, lifts, 
                               startedNodes, nextLiftGuid, stack, proposer, 
                               cycle, liftValue_P, arbitrator_P, nextPeer_, 
                               liftGuid, from_, to_, route_, liftValue_H, 
                               originator_, liftId_, arbitrator_H, prevPeer_, 
                               from_D, to_D, route_D, liftValue_D, 
                               originator_D, liftId_D, arbitrator_D, result_, 
                               from_C, to_C, route, liftValue, originator, 
                               liftId_C, arbitrator_C, result_C, to_R, 
                               liftId_R, result_R, prevPeer_R, timeout_, to_Re, 
                               liftId_Re, result, prevPeer, timeout, from_Co, 
                               to_Co, liftId_Co, nextPeer_C, liftValue_C, 
                               from_F, to, liftId_F, nextPeer, liftValue_F, 
                               from, liftId, arbitrator, cycle_, liftValue_, 
                               arbitrator_, toAct, lostMes >>

lchecktime_(self) == /\ pc[self] = "lchecktime_"
                     /\ \E validDecision \in {"Good", "Fail"}:
                          result_' = [result_ EXCEPT ![self] = validDecision]
                     /\ IF from_D[self] = originator_D[self]
                           THEN /\ lifts' = [lifts EXCEPT ![arbitrator_D[self]] = liftId_D[self] :> [originator |-> originator_D[self], value |-> liftValue_D[self], state |-> result_'[self], route |-> route_D[self], arbitrator |-> arbitrator_D[self]]]
                                /\ pc' = [pc EXCEPT ![self] = "lsm_D"]
                           ELSE /\ pc' = [pc EXCEPT ![self] = "lprintDecision_"]
                                /\ lifts' = lifts
                     /\ UNCHANGED << Users, LiftProposers, ReliableUsers, 
                                     Links, Cycles, tallies, messages, 
                                     readMessages, lostMessages, startedNodes, 
                                     nextLiftGuid, stack, proposer, cycle, 
                                     liftValue_P, arbitrator_P, nextPeer_, 
                                     liftGuid, from_, to_, route_, liftValue_H, 
                                     originator_, liftId_, arbitrator_H, 
                                     prevPeer_, from_D, to_D, route_D, 
                                     liftValue_D, originator_D, liftId_D, 
                                     arbitrator_D, from_C, to_C, route, 
                                     liftValue, originator, liftId_C, 
                                     arbitrator_C, result_C, to_R, liftId_R, 
                                     result_R, prevPeer_R, timeout_, to_Re, 
                                     liftId_Re, result, prevPeer, timeout, 
                                     from_Co, to_Co, liftId_Co, nextPeer_C, 
                                     liftValue_C, from_F, to, liftId_F, 
                                     nextPeer, liftValue_F, from, liftId, 
                                     arbitrator, cycle_, liftValue_, 
                                     arbitrator_, toAct, lostMes, printBuffer >>

lsm_D(self) == /\ pc[self] = "lsm_D"
               /\ IF MESSAGES_FAIL
                     THEN /\ \E messageWorks \in {TRUE, FALSE}:
                               IF messageWorks \/ ([from |-> to_D[self], to |-> from_D[self], type |-> "LiftValidResultJSON", liftId |-> liftId_D[self], result |-> result_[self]]).to \in ReliableUsers \/ ([from |-> to_D[self], to |-> from_D[self], type |-> "LiftValidResultJSON", liftId |-> liftId_D[self], result |-> result_[self]]).from \in ReliableUsers
                                  THEN /\ messages' = UNION{messages, {([from |-> to_D[self], to |-> from_D[self], type |-> "LiftValidResultJSON", liftId |-> liftId_D[self], result |-> result_[self]])}}
                                       /\ UNCHANGED << lostMessages, 
                                                       printBuffer >>
                                  ELSE /\ printBuffer' = [printBuffer EXCEPT ![self] = Append(printBuffer[self], "Message Failed")]
                                       /\ messages' = UNION{messages, {([from |-> to_D[self], to |-> from_D[self], type |-> "LiftValidResultJSON", liftId |-> liftId_D[self], result |-> result_[self]])}}
                                       /\ lostMessages' = UNION{lostMessages, {([from |-> to_D[self], to |-> from_D[self], type |-> "LiftValidResultJSON", liftId |-> liftId_D[self], result |-> result_[self]])}}
                     ELSE /\ messages' = UNION{messages, {([from |-> to_D[self], to |-> from_D[self], type |-> "LiftValidResultJSON", liftId |-> liftId_D[self], result |-> result_[self]])}}
                          /\ UNCHANGED << lostMessages, printBuffer >>
               /\ pc' = [pc EXCEPT ![self] = "lprintDecision_"]
               /\ UNCHANGED << Users, LiftProposers, ReliableUsers, Links, 
                               Cycles, tallies, readMessages, lifts, 
                               startedNodes, nextLiftGuid, stack, proposer, 
                               cycle, liftValue_P, arbitrator_P, nextPeer_, 
                               liftGuid, from_, to_, route_, liftValue_H, 
                               originator_, liftId_, arbitrator_H, prevPeer_, 
                               from_D, to_D, route_D, liftValue_D, 
                               originator_D, liftId_D, arbitrator_D, result_, 
                               from_C, to_C, route, liftValue, originator, 
                               liftId_C, arbitrator_C, result_C, to_R, 
                               liftId_R, result_R, prevPeer_R, timeout_, to_Re, 
                               liftId_Re, result, prevPeer, timeout, from_Co, 
                               to_Co, liftId_Co, nextPeer_C, liftValue_C, 
                               from_F, to, liftId_F, nextPeer, liftValue_F, 
                               from, liftId, arbitrator, cycle_, liftValue_, 
                               arbitrator_, toAct, lostMes >>

lprintDecision_(self) == /\ pc[self] = "lprintDecision_"
                         /\ printBuffer' = [printBuffer EXCEPT ![self] = Append(printBuffer[self], result_[self])]
                         /\ pc' = [pc EXCEPT ![self] = "DLVR_"]
                         /\ UNCHANGED << Users, LiftProposers, ReliableUsers, 
                                         Links, Cycles, tallies, messages, 
                                         readMessages, lostMessages, lifts, 
                                         startedNodes, nextLiftGuid, stack, 
                                         proposer, cycle, liftValue_P, 
                                         arbitrator_P, nextPeer_, liftGuid, 
                                         from_, to_, route_, liftValue_H, 
                                         originator_, liftId_, arbitrator_H, 
                                         prevPeer_, from_D, to_D, route_D, 
                                         liftValue_D, originator_D, liftId_D, 
                                         arbitrator_D, result_, from_C, to_C, 
                                         route, liftValue, originator, 
                                         liftId_C, arbitrator_C, result_C, 
                                         to_R, liftId_R, result_R, prevPeer_R, 
                                         timeout_, to_Re, liftId_Re, result, 
                                         prevPeer, timeout, from_Co, to_Co, 
                                         liftId_Co, nextPeer_C, liftValue_C, 
                                         from_F, to, liftId_F, nextPeer, 
                                         liftValue_F, from, liftId, arbitrator, 
                                         cycle_, liftValue_, arbitrator_, 
                                         toAct, lostMes >>

DLVR_(self) == /\ pc[self] = "DLVR_"
               /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
               /\ result_' = [result_ EXCEPT ![self] = Head(stack[self]).result_]
               /\ from_D' = [from_D EXCEPT ![self] = Head(stack[self]).from_D]
               /\ to_D' = [to_D EXCEPT ![self] = Head(stack[self]).to_D]
               /\ route_D' = [route_D EXCEPT ![self] = Head(stack[self]).route_D]
               /\ liftValue_D' = [liftValue_D EXCEPT ![self] = Head(stack[self]).liftValue_D]
               /\ originator_D' = [originator_D EXCEPT ![self] = Head(stack[self]).originator_D]
               /\ liftId_D' = [liftId_D EXCEPT ![self] = Head(stack[self]).liftId_D]
               /\ arbitrator_D' = [arbitrator_D EXCEPT ![self] = Head(stack[self]).arbitrator_D]
               /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
               /\ UNCHANGED << Users, LiftProposers, ReliableUsers, Links, 
                               Cycles, tallies, messages, readMessages, 
                               lostMessages, lifts, startedNodes, nextLiftGuid, 
                               proposer, cycle, liftValue_P, arbitrator_P, 
                               nextPeer_, liftGuid, from_, to_, route_, 
                               liftValue_H, originator_, liftId_, arbitrator_H, 
                               prevPeer_, from_C, to_C, route, liftValue, 
                               originator, liftId_C, arbitrator_C, result_C, 
                               to_R, liftId_R, result_R, prevPeer_R, timeout_, 
                               to_Re, liftId_Re, result, prevPeer, timeout, 
                               from_Co, to_Co, liftId_Co, nextPeer_C, 
                               liftValue_C, from_F, to, liftId_F, nextPeer, 
                               liftValue_F, from, liftId, arbitrator, cycle_, 
                               liftValue_, arbitrator_, toAct, lostMes, 
                               printBuffer >>

DecideLiftValidity(self) == DecideLiftValidity_(self) \/ lsom_(self)
                               \/ lchecktime_(self) \/ lsm_D(self)
                               \/ lprintDecision_(self) \/ DLVR_(self)

CkeckLiftValidity(self) == /\ pc[self] = "CkeckLiftValidity"
                           /\ printBuffer' = [printBuffer EXCEPT ![self] = Append(printBuffer[self], "Checking Lift Validity")]
                           /\ IF liftId_C[self] \notin DOMAIN lifts[arbitrator_C[self]] \/ (liftId_C[self] \in DOMAIN lifts[arbitrator_C[self]] /\ lifts[arbitrator_C[self]][liftId_C[self]].state = "Seek")
                                 THEN /\ IF \E lm \in lostMessages : lm.liftId = liftId_C[self]
                                            THEN /\ result_C' = [result_C EXCEPT ![self] = "Fail"]
                                                 /\ pc' = [pc EXCEPT ![self] = "lsr"]
                                            ELSE /\ pc' = [pc EXCEPT ![self] = "lchecktime"]
                                                 /\ UNCHANGED result_C
                                 ELSE /\ result_C' = [result_C EXCEPT ![self] = lifts[arbitrator_C[self]][liftId_C[self]].state]
                                      /\ pc' = [pc EXCEPT ![self] = "lsom"]
                           /\ UNCHANGED << Users, LiftProposers, ReliableUsers, 
                                           Links, Cycles, tallies, messages, 
                                           readMessages, lostMessages, lifts, 
                                           startedNodes, nextLiftGuid, stack, 
                                           proposer, cycle, liftValue_P, 
                                           arbitrator_P, nextPeer_, liftGuid, 
                                           from_, to_, route_, liftValue_H, 
                                           originator_, liftId_, arbitrator_H, 
                                           prevPeer_, from_D, to_D, route_D, 
                                           liftValue_D, originator_D, liftId_D, 
                                           arbitrator_D, result_, from_C, to_C, 
                                           route, liftValue, originator, 
                                           liftId_C, arbitrator_C, to_R, 
                                           liftId_R, result_R, prevPeer_R, 
                                           timeout_, to_Re, liftId_Re, result, 
                                           prevPeer, timeout, from_Co, to_Co, 
                                           liftId_Co, nextPeer_C, liftValue_C, 
                                           from_F, to, liftId_F, nextPeer, 
                                           liftValue_F, from, liftId, 
                                           arbitrator, cycle_, liftValue_, 
                                           arbitrator_, toAct, lostMes >>

lsr(self) == /\ pc[self] = "lsr"
             /\ lifts' = [lifts EXCEPT ![arbitrator_C[self]] = liftId_C[self] :> [originator |-> originator[self], value |-> liftValue[self], state |-> result_C[self], route |-> route[self], arbitrator |-> arbitrator_C[self]]]
             /\ pc' = [pc EXCEPT ![self] = "lsm2"]
             /\ UNCHANGED << Users, LiftProposers, ReliableUsers, Links, 
                             Cycles, tallies, messages, readMessages, 
                             lostMessages, startedNodes, nextLiftGuid, stack, 
                             proposer, cycle, liftValue_P, arbitrator_P, 
                             nextPeer_, liftGuid, from_, to_, route_, 
                             liftValue_H, originator_, liftId_, arbitrator_H, 
                             prevPeer_, from_D, to_D, route_D, liftValue_D, 
                             originator_D, liftId_D, arbitrator_D, result_, 
                             from_C, to_C, route, liftValue, originator, 
                             liftId_C, arbitrator_C, result_C, to_R, liftId_R, 
                             result_R, prevPeer_R, timeout_, to_Re, liftId_Re, 
                             result, prevPeer, timeout, from_Co, to_Co, 
                             liftId_Co, nextPeer_C, liftValue_C, from_F, to, 
                             liftId_F, nextPeer, liftValue_F, from, liftId, 
                             arbitrator, cycle_, liftValue_, arbitrator_, 
                             toAct, lostMes, printBuffer >>

lsm2(self) == /\ pc[self] = "lsm2"
              /\ IF MESSAGES_FAIL
                    THEN /\ \E messageWorks \in {TRUE, FALSE}:
                              IF messageWorks \/ ([from |-> to_C[self], to |-> from_C[self], type |-> "LiftCheckResultJSON", liftId |-> liftId_C[self], result |-> result_C[self]]).to \in ReliableUsers \/ ([from |-> to_C[self], to |-> from_C[self], type |-> "LiftCheckResultJSON", liftId |-> liftId_C[self], result |-> result_C[self]]).from \in ReliableUsers
                                 THEN /\ messages' = UNION{messages, {([from |-> to_C[self], to |-> from_C[self], type |-> "LiftCheckResultJSON", liftId |-> liftId_C[self], result |-> result_C[self]])}}
                                      /\ UNCHANGED << lostMessages, 
                                                      printBuffer >>
                                 ELSE /\ printBuffer' = [printBuffer EXCEPT ![self] = Append(printBuffer[self], "Message Failed")]
                                      /\ messages' = UNION{messages, {([from |-> to_C[self], to |-> from_C[self], type |-> "LiftCheckResultJSON", liftId |-> liftId_C[self], result |-> result_C[self]])}}
                                      /\ lostMessages' = UNION{lostMessages, {([from |-> to_C[self], to |-> from_C[self], type |-> "LiftCheckResultJSON", liftId |-> liftId_C[self], result |-> result_C[self]])}}
                    ELSE /\ messages' = UNION{messages, {([from |-> to_C[self], to |-> from_C[self], type |-> "LiftCheckResultJSON", liftId |-> liftId_C[self], result |-> result_C[self]])}}
                         /\ UNCHANGED << lostMessages, printBuffer >>
              /\ pc' = [pc EXCEPT ![self] = "lprintDecision"]
              /\ UNCHANGED << Users, LiftProposers, ReliableUsers, Links, 
                              Cycles, tallies, readMessages, lifts, 
                              startedNodes, nextLiftGuid, stack, proposer, 
                              cycle, liftValue_P, arbitrator_P, nextPeer_, 
                              liftGuid, from_, to_, route_, liftValue_H, 
                              originator_, liftId_, arbitrator_H, prevPeer_, 
                              from_D, to_D, route_D, liftValue_D, originator_D, 
                              liftId_D, arbitrator_D, result_, from_C, to_C, 
                              route, liftValue, originator, liftId_C, 
                              arbitrator_C, result_C, to_R, liftId_R, result_R, 
                              prevPeer_R, timeout_, to_Re, liftId_Re, result, 
                              prevPeer, timeout, from_Co, to_Co, liftId_Co, 
                              nextPeer_C, liftValue_C, from_F, to, liftId_F, 
                              nextPeer, liftValue_F, from, liftId, arbitrator, 
                              cycle_, liftValue_, arbitrator_, toAct, lostMes >>

lsom(self) == /\ pc[self] = "lsom"
              /\ IF MESSAGES_FAIL
                    THEN /\ \E messageWorks \in {TRUE, FALSE}:
                              IF messageWorks \/ ([from |-> to_C[self], to |-> from_C[self], type |-> "LiftCheckResultJSON", liftId |-> liftId_C[self], result |-> result_C[self]]).to \in ReliableUsers \/ ([from |-> to_C[self], to |-> from_C[self], type |-> "LiftCheckResultJSON", liftId |-> liftId_C[self], result |-> result_C[self]]).from \in ReliableUsers
                                 THEN /\ messages' = UNION{messages, {([from |-> to_C[self], to |-> from_C[self], type |-> "LiftCheckResultJSON", liftId |-> liftId_C[self], result |-> result_C[self]])}}
                                      /\ UNCHANGED << lostMessages, 
                                                      printBuffer >>
                                 ELSE /\ printBuffer' = [printBuffer EXCEPT ![self] = Append(printBuffer[self], "Message Failed")]
                                      /\ messages' = UNION{messages, {([from |-> to_C[self], to |-> from_C[self], type |-> "LiftCheckResultJSON", liftId |-> liftId_C[self], result |-> result_C[self]])}}
                                      /\ lostMessages' = UNION{lostMessages, {([from |-> to_C[self], to |-> from_C[self], type |-> "LiftCheckResultJSON", liftId |-> liftId_C[self], result |-> result_C[self]])}}
                    ELSE /\ messages' = UNION{messages, {([from |-> to_C[self], to |-> from_C[self], type |-> "LiftCheckResultJSON", liftId |-> liftId_C[self], result |-> result_C[self]])}}
                         /\ UNCHANGED << lostMessages, printBuffer >>
              /\ pc' = [pc EXCEPT ![self] = "lprintDecision"]
              /\ UNCHANGED << Users, LiftProposers, ReliableUsers, Links, 
                              Cycles, tallies, readMessages, lifts, 
                              startedNodes, nextLiftGuid, stack, proposer, 
                              cycle, liftValue_P, arbitrator_P, nextPeer_, 
                              liftGuid, from_, to_, route_, liftValue_H, 
                              originator_, liftId_, arbitrator_H, prevPeer_, 
                              from_D, to_D, route_D, liftValue_D, originator_D, 
                              liftId_D, arbitrator_D, result_, from_C, to_C, 
                              route, liftValue, originator, liftId_C, 
                              arbitrator_C, result_C, to_R, liftId_R, result_R, 
                              prevPeer_R, timeout_, to_Re, liftId_Re, result, 
                              prevPeer, timeout, from_Co, to_Co, liftId_Co, 
                              nextPeer_C, liftValue_C, from_F, to, liftId_F, 
                              nextPeer, liftValue_F, from, liftId, arbitrator, 
                              cycle_, liftValue_, arbitrator_, toAct, lostMes >>

lchecktime(self) == /\ pc[self] = "lchecktime"
                    /\ \E validDecision \in {"Seek", "Fail"}:
                         result_C' = [result_C EXCEPT ![self] = validDecision]
                    /\ pc' = [pc EXCEPT ![self] = "lsr"]
                    /\ UNCHANGED << Users, LiftProposers, ReliableUsers, Links, 
                                    Cycles, tallies, messages, readMessages, 
                                    lostMessages, lifts, startedNodes, 
                                    nextLiftGuid, stack, proposer, cycle, 
                                    liftValue_P, arbitrator_P, nextPeer_, 
                                    liftGuid, from_, to_, route_, liftValue_H, 
                                    originator_, liftId_, arbitrator_H, 
                                    prevPeer_, from_D, to_D, route_D, 
                                    liftValue_D, originator_D, liftId_D, 
                                    arbitrator_D, result_, from_C, to_C, route, 
                                    liftValue, originator, liftId_C, 
                                    arbitrator_C, to_R, liftId_R, result_R, 
                                    prevPeer_R, timeout_, to_Re, liftId_Re, 
                                    result, prevPeer, timeout, from_Co, to_Co, 
                                    liftId_Co, nextPeer_C, liftValue_C, from_F, 
                                    to, liftId_F, nextPeer, liftValue_F, from, 
                                    liftId, arbitrator, cycle_, liftValue_, 
                                    arbitrator_, toAct, lostMes, printBuffer >>

lprintDecision(self) == /\ pc[self] = "lprintDecision"
                        /\ printBuffer' = [printBuffer EXCEPT ![self] = Append(printBuffer[self], result_C[self])]
                        /\ pc' = [pc EXCEPT ![self] = "DLVR"]
                        /\ UNCHANGED << Users, LiftProposers, ReliableUsers, 
                                        Links, Cycles, tallies, messages, 
                                        readMessages, lostMessages, lifts, 
                                        startedNodes, nextLiftGuid, stack, 
                                        proposer, cycle, liftValue_P, 
                                        arbitrator_P, nextPeer_, liftGuid, 
                                        from_, to_, route_, liftValue_H, 
                                        originator_, liftId_, arbitrator_H, 
                                        prevPeer_, from_D, to_D, route_D, 
                                        liftValue_D, originator_D, liftId_D, 
                                        arbitrator_D, result_, from_C, to_C, 
                                        route, liftValue, originator, liftId_C, 
                                        arbitrator_C, result_C, to_R, liftId_R, 
                                        result_R, prevPeer_R, timeout_, to_Re, 
                                        liftId_Re, result, prevPeer, timeout, 
                                        from_Co, to_Co, liftId_Co, nextPeer_C, 
                                        liftValue_C, from_F, to, liftId_F, 
                                        nextPeer, liftValue_F, from, liftId, 
                                        arbitrator, cycle_, liftValue_, 
                                        arbitrator_, toAct, lostMes >>

DLVR(self) == /\ pc[self] = "DLVR"
              /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
              /\ result_C' = [result_C EXCEPT ![self] = Head(stack[self]).result_C]
              /\ from_C' = [from_C EXCEPT ![self] = Head(stack[self]).from_C]
              /\ to_C' = [to_C EXCEPT ![self] = Head(stack[self]).to_C]
              /\ route' = [route EXCEPT ![self] = Head(stack[self]).route]
              /\ liftValue' = [liftValue EXCEPT ![self] = Head(stack[self]).liftValue]
              /\ originator' = [originator EXCEPT ![self] = Head(stack[self]).originator]
              /\ liftId_C' = [liftId_C EXCEPT ![self] = Head(stack[self]).liftId_C]
              /\ arbitrator_C' = [arbitrator_C EXCEPT ![self] = Head(stack[self]).arbitrator_C]
              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
              /\ UNCHANGED << Users, LiftProposers, ReliableUsers, Links, 
                              Cycles, tallies, messages, readMessages, 
                              lostMessages, lifts, startedNodes, nextLiftGuid, 
                              proposer, cycle, liftValue_P, arbitrator_P, 
                              nextPeer_, liftGuid, from_, to_, route_, 
                              liftValue_H, originator_, liftId_, arbitrator_H, 
                              prevPeer_, from_D, to_D, route_D, liftValue_D, 
                              originator_D, liftId_D, arbitrator_D, result_, 
                              to_R, liftId_R, result_R, prevPeer_R, timeout_, 
                              to_Re, liftId_Re, result, prevPeer, timeout, 
                              from_Co, to_Co, liftId_Co, nextPeer_C, 
                              liftValue_C, from_F, to, liftId_F, nextPeer, 
                              liftValue_F, from, liftId, arbitrator, cycle_, 
                              liftValue_, arbitrator_, toAct, lostMes, 
                              printBuffer >>

CheckLiftValidity(self) == CkeckLiftValidity(self) \/ lsr(self)
                              \/ lsm2(self) \/ lsom(self)
                              \/ lchecktime(self) \/ lprintDecision(self)
                              \/ DLVR(self)

ValidateLift_(self) == /\ pc[self] = "ValidateLift_"
                       /\ printBuffer' = [printBuffer EXCEPT ![self] = Append(printBuffer[self], "Receiving Lift Valid Response")]
                       /\ prevPeer_R' = [prevPeer_R EXCEPT ![self] = NextElemIn(to_R[self], lifts[to_R[self]][liftId_R[self]].route)]
                       /\ IF result_R[self] = "Fail"
                             THEN /\ pc' = [pc EXCEPT ![self] = "lpt_"]
                             ELSE /\ IF to_R[self] = lifts[to_R[self]][liftId_R[self]].originator
                                        THEN /\ pc' = [pc EXCEPT ![self] = "lpv"]
                                        ELSE /\ pc' = [pc EXCEPT ![self] = "VLR_"]
                       /\ UNCHANGED << Users, LiftProposers, ReliableUsers, 
                                       Links, Cycles, tallies, messages, 
                                       readMessages, lostMessages, lifts, 
                                       startedNodes, nextLiftGuid, stack, 
                                       proposer, cycle, liftValue_P, 
                                       arbitrator_P, nextPeer_, liftGuid, 
                                       from_, to_, route_, liftValue_H, 
                                       originator_, liftId_, arbitrator_H, 
                                       prevPeer_, from_D, to_D, route_D, 
                                       liftValue_D, originator_D, liftId_D, 
                                       arbitrator_D, result_, from_C, to_C, 
                                       route, liftValue, originator, liftId_C, 
                                       arbitrator_C, result_C, to_R, liftId_R, 
                                       result_R, timeout_, to_Re, liftId_Re, 
                                       result, prevPeer, timeout, from_Co, 
                                       to_Co, liftId_Co, nextPeer_C, 
                                       liftValue_C, from_F, to, liftId_F, 
                                       nextPeer, liftValue_F, from, liftId, 
                                       arbitrator, cycle_, liftValue_, 
                                       arbitrator_, toAct, lostMes >>

lpt_(self) == /\ pc[self] = "lpt_"
              /\ printBuffer' = [printBuffer EXCEPT ![self] = Append(printBuffer[self], "Lift Invalid")]
              /\ pc' = [pc EXCEPT ![self] = "lsm1"]
              /\ UNCHANGED << Users, LiftProposers, ReliableUsers, Links, 
                              Cycles, tallies, messages, readMessages, 
                              lostMessages, lifts, startedNodes, nextLiftGuid, 
                              stack, proposer, cycle, liftValue_P, 
                              arbitrator_P, nextPeer_, liftGuid, from_, to_, 
                              route_, liftValue_H, originator_, liftId_, 
                              arbitrator_H, prevPeer_, from_D, to_D, route_D, 
                              liftValue_D, originator_D, liftId_D, 
                              arbitrator_D, result_, from_C, to_C, route, 
                              liftValue, originator, liftId_C, arbitrator_C, 
                              result_C, to_R, liftId_R, result_R, prevPeer_R, 
                              timeout_, to_Re, liftId_Re, result, prevPeer, 
                              timeout, from_Co, to_Co, liftId_Co, nextPeer_C, 
                              liftValue_C, from_F, to, liftId_F, nextPeer, 
                              liftValue_F, from, liftId, arbitrator, cycle_, 
                              liftValue_, arbitrator_, toAct, lostMes >>

lsm1(self) == /\ pc[self] = "lsm1"
              /\ IF MESSAGES_FAIL
                    THEN /\ \E messageWorks \in {TRUE, FALSE}:
                              IF messageWorks \/ ([liftId |-> liftId_R[self], from |-> to_R[self], to |-> prevPeer_R[self], type |-> "LiftFailJSON"]).to \in ReliableUsers \/ ([liftId |-> liftId_R[self], from |-> to_R[self], to |-> prevPeer_R[self], type |-> "LiftFailJSON"]).from \in ReliableUsers
                                 THEN /\ messages' = UNION{messages, {([liftId |-> liftId_R[self], from |-> to_R[self], to |-> prevPeer_R[self], type |-> "LiftFailJSON"])}}
                                      /\ UNCHANGED << lostMessages, 
                                                      printBuffer >>
                                 ELSE /\ printBuffer' = [printBuffer EXCEPT ![self] = Append(printBuffer[self], "Message Failed")]
                                      /\ messages' = UNION{messages, {([liftId |-> liftId_R[self], from |-> to_R[self], to |-> prevPeer_R[self], type |-> "LiftFailJSON"])}}
                                      /\ lostMessages' = UNION{lostMessages, {([liftId |-> liftId_R[self], from |-> to_R[self], to |-> prevPeer_R[self], type |-> "LiftFailJSON"])}}
                    ELSE /\ messages' = UNION{messages, {([liftId |-> liftId_R[self], from |-> to_R[self], to |-> prevPeer_R[self], type |-> "LiftFailJSON"])}}
                         /\ UNCHANGED << lostMessages, printBuffer >>
              /\ pc' = [pc EXCEPT ![self] = "L1"]
              /\ UNCHANGED << Users, LiftProposers, ReliableUsers, Links, 
                              Cycles, tallies, readMessages, lifts, 
                              startedNodes, nextLiftGuid, stack, proposer, 
                              cycle, liftValue_P, arbitrator_P, nextPeer_, 
                              liftGuid, from_, to_, route_, liftValue_H, 
                              originator_, liftId_, arbitrator_H, prevPeer_, 
                              from_D, to_D, route_D, liftValue_D, originator_D, 
                              liftId_D, arbitrator_D, result_, from_C, to_C, 
                              route, liftValue, originator, liftId_C, 
                              arbitrator_C, result_C, to_R, liftId_R, result_R, 
                              prevPeer_R, timeout_, to_Re, liftId_Re, result, 
                              prevPeer, timeout, from_Co, to_Co, liftId_Co, 
                              nextPeer_C, liftValue_C, from_F, to, liftId_F, 
                              nextPeer, liftValue_F, from, liftId, arbitrator, 
                              cycle_, liftValue_, arbitrator_, toAct, lostMes >>

L1(self) == /\ pc[self] = "L1"
            /\ tallies' = [tallies EXCEPT ![<<to_R[self], prevPeer_R[self], "Foil">>].projectedBalance = tallies[<<to_R[self], prevPeer_R[self], "Foil">>].projectedBalance - lifts[to_R[self]][liftId_R[self]].value]
            /\ pc' = [pc EXCEPT ![self] = "VLR_"]
            /\ UNCHANGED << Users, LiftProposers, ReliableUsers, Links, Cycles, 
                            messages, readMessages, lostMessages, lifts, 
                            startedNodes, nextLiftGuid, stack, proposer, cycle, 
                            liftValue_P, arbitrator_P, nextPeer_, liftGuid, 
                            from_, to_, route_, liftValue_H, originator_, 
                            liftId_, arbitrator_H, prevPeer_, from_D, to_D, 
                            route_D, liftValue_D, originator_D, liftId_D, 
                            arbitrator_D, result_, from_C, to_C, route, 
                            liftValue, originator, liftId_C, arbitrator_C, 
                            result_C, to_R, liftId_R, result_R, prevPeer_R, 
                            timeout_, to_Re, liftId_Re, result, prevPeer, 
                            timeout, from_Co, to_Co, liftId_Co, nextPeer_C, 
                            liftValue_C, from_F, to, liftId_F, nextPeer, 
                            liftValue_F, from, liftId, arbitrator, cycle_, 
                            liftValue_, arbitrator_, toAct, lostMes, 
                            printBuffer >>

lpv(self) == /\ pc[self] = "lpv"
             /\ printBuffer' = [printBuffer EXCEPT ![self] = Append(printBuffer[self], "Lift Valid")]
             /\ pc' = [pc EXCEPT ![self] = "lsm"]
             /\ UNCHANGED << Users, LiftProposers, ReliableUsers, Links, 
                             Cycles, tallies, messages, readMessages, 
                             lostMessages, lifts, startedNodes, nextLiftGuid, 
                             stack, proposer, cycle, liftValue_P, arbitrator_P, 
                             nextPeer_, liftGuid, from_, to_, route_, 
                             liftValue_H, originator_, liftId_, arbitrator_H, 
                             prevPeer_, from_D, to_D, route_D, liftValue_D, 
                             originator_D, liftId_D, arbitrator_D, result_, 
                             from_C, to_C, route, liftValue, originator, 
                             liftId_C, arbitrator_C, result_C, to_R, liftId_R, 
                             result_R, prevPeer_R, timeout_, to_Re, liftId_Re, 
                             result, prevPeer, timeout, from_Co, to_Co, 
                             liftId_Co, nextPeer_C, liftValue_C, from_F, to, 
                             liftId_F, nextPeer, liftValue_F, from, liftId, 
                             arbitrator, cycle_, liftValue_, arbitrator_, 
                             toAct, lostMes >>

lsm(self) == /\ pc[self] = "lsm"
             /\ IF MESSAGES_FAIL
                   THEN /\ \E messageWorks \in {TRUE, FALSE}:
                             IF messageWorks \/ ([liftId |-> liftId_R[self], from |-> to_R[self], to |-> prevPeer_R[self], type |-> "LiftCommitJSON"]).to \in ReliableUsers \/ ([liftId |-> liftId_R[self], from |-> to_R[self], to |-> prevPeer_R[self], type |-> "LiftCommitJSON"]).from \in ReliableUsers
                                THEN /\ messages' = UNION{messages, {([liftId |-> liftId_R[self], from |-> to_R[self], to |-> prevPeer_R[self], type |-> "LiftCommitJSON"])}}
                                     /\ UNCHANGED << lostMessages, printBuffer >>
                                ELSE /\ printBuffer' = [printBuffer EXCEPT ![self] = Append(printBuffer[self], "Message Failed")]
                                     /\ messages' = UNION{messages, {([liftId |-> liftId_R[self], from |-> to_R[self], to |-> prevPeer_R[self], type |-> "LiftCommitJSON"])}}
                                     /\ lostMessages' = UNION{lostMessages, {([liftId |-> liftId_R[self], from |-> to_R[self], to |-> prevPeer_R[self], type |-> "LiftCommitJSON"])}}
                   ELSE /\ messages' = UNION{messages, {([liftId |-> liftId_R[self], from |-> to_R[self], to |-> prevPeer_R[self], type |-> "LiftCommitJSON"])}}
                        /\ UNCHANGED << lostMessages, printBuffer >>
             /\ pc' = [pc EXCEPT ![self] = "L2"]
             /\ UNCHANGED << Users, LiftProposers, ReliableUsers, Links, 
                             Cycles, tallies, readMessages, lifts, 
                             startedNodes, nextLiftGuid, stack, proposer, 
                             cycle, liftValue_P, arbitrator_P, nextPeer_, 
                             liftGuid, from_, to_, route_, liftValue_H, 
                             originator_, liftId_, arbitrator_H, prevPeer_, 
                             from_D, to_D, route_D, liftValue_D, originator_D, 
                             liftId_D, arbitrator_D, result_, from_C, to_C, 
                             route, liftValue, originator, liftId_C, 
                             arbitrator_C, result_C, to_R, liftId_R, result_R, 
                             prevPeer_R, timeout_, to_Re, liftId_Re, result, 
                             prevPeer, timeout, from_Co, to_Co, liftId_Co, 
                             nextPeer_C, liftValue_C, from_F, to, liftId_F, 
                             nextPeer, liftValue_F, from, liftId, arbitrator, 
                             cycle_, liftValue_, arbitrator_, toAct, lostMes >>

L2(self) == /\ pc[self] = "L2"
            /\ tallies' = [tallies EXCEPT ![<<to_R[self], prevPeer_R[self], "Foil">>].balance = tallies[<<to_R[self], prevPeer_R[self], "Foil">>].balance + lifts[to_R[self]][liftId_R[self]].value]
            /\ pc' = [pc EXCEPT ![self] = "VLR_"]
            /\ UNCHANGED << Users, LiftProposers, ReliableUsers, Links, Cycles, 
                            messages, readMessages, lostMessages, lifts, 
                            startedNodes, nextLiftGuid, stack, proposer, cycle, 
                            liftValue_P, arbitrator_P, nextPeer_, liftGuid, 
                            from_, to_, route_, liftValue_H, originator_, 
                            liftId_, arbitrator_H, prevPeer_, from_D, to_D, 
                            route_D, liftValue_D, originator_D, liftId_D, 
                            arbitrator_D, result_, from_C, to_C, route, 
                            liftValue, originator, liftId_C, arbitrator_C, 
                            result_C, to_R, liftId_R, result_R, prevPeer_R, 
                            timeout_, to_Re, liftId_Re, result, prevPeer, 
                            timeout, from_Co, to_Co, liftId_Co, nextPeer_C, 
                            liftValue_C, from_F, to, liftId_F, nextPeer, 
                            liftValue_F, from, liftId, arbitrator, cycle_, 
                            liftValue_, arbitrator_, toAct, lostMes, 
                            printBuffer >>

VLR_(self) == /\ pc[self] = "VLR_"
              /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
              /\ prevPeer_R' = [prevPeer_R EXCEPT ![self] = Head(stack[self]).prevPeer_R]
              /\ timeout_' = [timeout_ EXCEPT ![self] = Head(stack[self]).timeout_]
              /\ to_R' = [to_R EXCEPT ![self] = Head(stack[self]).to_R]
              /\ liftId_R' = [liftId_R EXCEPT ![self] = Head(stack[self]).liftId_R]
              /\ result_R' = [result_R EXCEPT ![self] = Head(stack[self]).result_R]
              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
              /\ UNCHANGED << Users, LiftProposers, ReliableUsers, Links, 
                              Cycles, tallies, messages, readMessages, 
                              lostMessages, lifts, startedNodes, nextLiftGuid, 
                              proposer, cycle, liftValue_P, arbitrator_P, 
                              nextPeer_, liftGuid, from_, to_, route_, 
                              liftValue_H, originator_, liftId_, arbitrator_H, 
                              prevPeer_, from_D, to_D, route_D, liftValue_D, 
                              originator_D, liftId_D, arbitrator_D, result_, 
                              from_C, to_C, route, liftValue, originator, 
                              liftId_C, arbitrator_C, result_C, to_Re, 
                              liftId_Re, result, prevPeer, timeout, from_Co, 
                              to_Co, liftId_Co, nextPeer_C, liftValue_C, 
                              from_F, to, liftId_F, nextPeer, liftValue_F, 
                              from, liftId, arbitrator, cycle_, liftValue_, 
                              arbitrator_, toAct, lostMes, printBuffer >>

ReceiveLiftValidResult(self) == ValidateLift_(self) \/ lpt_(self)
                                   \/ lsm1(self) \/ L1(self) \/ lpv(self)
                                   \/ lsm(self) \/ L2(self) \/ VLR_(self)

ValidateLift(self) == /\ pc[self] = "ValidateLift"
                      /\ printBuffer' = [printBuffer EXCEPT ![self] = Append(printBuffer[self], "Receving Lift Check Response")]
                      /\ prevPeer' = [prevPeer EXCEPT ![self] = NextElemIn(to_Re[self], lifts[to_Re[self]][liftId_Re[self]].route)]
                      /\ IF result[self] = "Fail"
                            THEN /\ pc' = [pc EXCEPT ![self] = "lpt"]
                            ELSE /\ pc' = [pc EXCEPT ![self] = "VLR"]
                      /\ UNCHANGED << Users, LiftProposers, ReliableUsers, 
                                      Links, Cycles, tallies, messages, 
                                      readMessages, lostMessages, lifts, 
                                      startedNodes, nextLiftGuid, stack, 
                                      proposer, cycle, liftValue_P, 
                                      arbitrator_P, nextPeer_, liftGuid, from_, 
                                      to_, route_, liftValue_H, originator_, 
                                      liftId_, arbitrator_H, prevPeer_, from_D, 
                                      to_D, route_D, liftValue_D, originator_D, 
                                      liftId_D, arbitrator_D, result_, from_C, 
                                      to_C, route, liftValue, originator, 
                                      liftId_C, arbitrator_C, result_C, to_R, 
                                      liftId_R, result_R, prevPeer_R, timeout_, 
                                      to_Re, liftId_Re, result, timeout, 
                                      from_Co, to_Co, liftId_Co, nextPeer_C, 
                                      liftValue_C, from_F, to, liftId_F, 
                                      nextPeer, liftValue_F, from, liftId, 
                                      arbitrator, cycle_, liftValue_, 
                                      arbitrator_, toAct, lostMes >>

lpt(self) == /\ pc[self] = "lpt"
             /\ printBuffer' = [printBuffer EXCEPT ![self] = Append(printBuffer[self], "Lift Invalid")]
             /\ /\ from_F' = [from_F EXCEPT ![self] = to_Re[self]]
                /\ liftId_F' = [liftId_F EXCEPT ![self] = liftId_Re[self]]
                /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "FailLift",
                                                         pc        |->  "VLR",
                                                         nextPeer  |->  nextPeer[self],
                                                         liftValue_F |->  liftValue_F[self],
                                                         from_F    |->  from_F[self],
                                                         to        |->  to[self],
                                                         liftId_F  |->  liftId_F[self] ] >>
                                                     \o stack[self]]
                /\ to' = [to EXCEPT ![self] = prevPeer[self]]
             /\ nextPeer' = [nextPeer EXCEPT ![self] = defaultInitValue]
             /\ liftValue_F' = [liftValue_F EXCEPT ![self] = defaultInitValue]
             /\ pc' = [pc EXCEPT ![self] = "FailLift_"]
             /\ UNCHANGED << Users, LiftProposers, ReliableUsers, Links, 
                             Cycles, tallies, messages, readMessages, 
                             lostMessages, lifts, startedNodes, nextLiftGuid, 
                             proposer, cycle, liftValue_P, arbitrator_P, 
                             nextPeer_, liftGuid, from_, to_, route_, 
                             liftValue_H, originator_, liftId_, arbitrator_H, 
                             prevPeer_, from_D, to_D, route_D, liftValue_D, 
                             originator_D, liftId_D, arbitrator_D, result_, 
                             from_C, to_C, route, liftValue, originator, 
                             liftId_C, arbitrator_C, result_C, to_R, liftId_R, 
                             result_R, prevPeer_R, timeout_, to_Re, liftId_Re, 
                             result, prevPeer, timeout, from_Co, to_Co, 
                             liftId_Co, nextPeer_C, liftValue_C, from, liftId, 
                             arbitrator, cycle_, liftValue_, arbitrator_, 
                             toAct, lostMes >>

VLR(self) == /\ pc[self] = "VLR"
             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
             /\ prevPeer' = [prevPeer EXCEPT ![self] = Head(stack[self]).prevPeer]
             /\ timeout' = [timeout EXCEPT ![self] = Head(stack[self]).timeout]
             /\ to_Re' = [to_Re EXCEPT ![self] = Head(stack[self]).to_Re]
             /\ liftId_Re' = [liftId_Re EXCEPT ![self] = Head(stack[self]).liftId_Re]
             /\ result' = [result EXCEPT ![self] = Head(stack[self]).result]
             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
             /\ UNCHANGED << Users, LiftProposers, ReliableUsers, Links, 
                             Cycles, tallies, messages, readMessages, 
                             lostMessages, lifts, startedNodes, nextLiftGuid, 
                             proposer, cycle, liftValue_P, arbitrator_P, 
                             nextPeer_, liftGuid, from_, to_, route_, 
                             liftValue_H, originator_, liftId_, arbitrator_H, 
                             prevPeer_, from_D, to_D, route_D, liftValue_D, 
                             originator_D, liftId_D, arbitrator_D, result_, 
                             from_C, to_C, route, liftValue, originator, 
                             liftId_C, arbitrator_C, result_C, to_R, liftId_R, 
                             result_R, prevPeer_R, timeout_, from_Co, to_Co, 
                             liftId_Co, nextPeer_C, liftValue_C, from_F, to, 
                             liftId_F, nextPeer, liftValue_F, from, liftId, 
                             arbitrator, cycle_, liftValue_, arbitrator_, 
                             toAct, lostMes, printBuffer >>

ReceiveLiftCheckResult(self) == ValidateLift(self) \/ lpt(self)
                                   \/ VLR(self)

CommitLift_(self) == /\ pc[self] = "CommitLift_"
                     /\ printBuffer' = [printBuffer EXCEPT ![self] = Append(printBuffer[self], "Commit Lift")]
                     /\ liftValue_C' = [liftValue_C EXCEPT ![self] = lifts[to_Co[self]][liftId_Co[self]].value]
                     /\ lifts' = [lifts EXCEPT ![to_Co[self]][liftId_Co[self]].state = "Good"]
                     /\ pc' = [pc EXCEPT ![self] = "CL2_"]
                     /\ UNCHANGED << Users, LiftProposers, ReliableUsers, 
                                     Links, Cycles, tallies, messages, 
                                     readMessages, lostMessages, startedNodes, 
                                     nextLiftGuid, stack, proposer, cycle, 
                                     liftValue_P, arbitrator_P, nextPeer_, 
                                     liftGuid, from_, to_, route_, liftValue_H, 
                                     originator_, liftId_, arbitrator_H, 
                                     prevPeer_, from_D, to_D, route_D, 
                                     liftValue_D, originator_D, liftId_D, 
                                     arbitrator_D, result_, from_C, to_C, 
                                     route, liftValue, originator, liftId_C, 
                                     arbitrator_C, result_C, to_R, liftId_R, 
                                     result_R, prevPeer_R, timeout_, to_Re, 
                                     liftId_Re, result, prevPeer, timeout, 
                                     from_Co, to_Co, liftId_Co, nextPeer_C, 
                                     from_F, to, liftId_F, nextPeer, 
                                     liftValue_F, from, liftId, arbitrator, 
                                     cycle_, liftValue_, arbitrator_, toAct, 
                                     lostMes >>

CL2_(self) == /\ pc[self] = "CL2_"
              /\ tallies' = [tallies EXCEPT ![<<to_Co[self], from_Co[self], "Stock">>].balance = tallies[<<to_Co[self], from_Co[self], "Stock">>].balance - liftValue_C[self]]
              /\ IF to_Co[self] /= lifts[to_Co[self]][liftId_Co[self]].originator
                    THEN /\ nextPeer_C' = [nextPeer_C EXCEPT ![self] = NextElemIn(to_Co[self], lifts[to_Co[self]][liftId_Co[self]].route)]
                         /\ pc' = [pc EXCEPT ![self] = "CL4_"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "CLR_"]
                         /\ UNCHANGED nextPeer_C
              /\ UNCHANGED << Users, LiftProposers, ReliableUsers, Links, 
                              Cycles, messages, readMessages, lostMessages, 
                              lifts, startedNodes, nextLiftGuid, stack, 
                              proposer, cycle, liftValue_P, arbitrator_P, 
                              nextPeer_, liftGuid, from_, to_, route_, 
                              liftValue_H, originator_, liftId_, arbitrator_H, 
                              prevPeer_, from_D, to_D, route_D, liftValue_D, 
                              originator_D, liftId_D, arbitrator_D, result_, 
                              from_C, to_C, route, liftValue, originator, 
                              liftId_C, arbitrator_C, result_C, to_R, liftId_R, 
                              result_R, prevPeer_R, timeout_, to_Re, liftId_Re, 
                              result, prevPeer, timeout, from_Co, to_Co, 
                              liftId_Co, liftValue_C, from_F, to, liftId_F, 
                              nextPeer, liftValue_F, from, liftId, arbitrator, 
                              cycle_, liftValue_, arbitrator_, toAct, lostMes, 
                              printBuffer >>

CL4_(self) == /\ pc[self] = "CL4_"
              /\ IF MESSAGES_FAIL
                    THEN /\ \E messageWorks \in {TRUE, FALSE}:
                              IF messageWorks \/ ([liftId |-> liftId_Co[self], from |-> to_Co[self], to |-> nextPeer_C[self], type |-> "LiftCommitJSON"]).to \in ReliableUsers \/ ([liftId |-> liftId_Co[self], from |-> to_Co[self], to |-> nextPeer_C[self], type |-> "LiftCommitJSON"]).from \in ReliableUsers
                                 THEN /\ messages' = UNION{messages, {([liftId |-> liftId_Co[self], from |-> to_Co[self], to |-> nextPeer_C[self], type |-> "LiftCommitJSON"])}}
                                      /\ UNCHANGED << lostMessages, 
                                                      printBuffer >>
                                 ELSE /\ printBuffer' = [printBuffer EXCEPT ![self] = Append(printBuffer[self], "Message Failed")]
                                      /\ messages' = UNION{messages, {([liftId |-> liftId_Co[self], from |-> to_Co[self], to |-> nextPeer_C[self], type |-> "LiftCommitJSON"])}}
                                      /\ lostMessages' = UNION{lostMessages, {([liftId |-> liftId_Co[self], from |-> to_Co[self], to |-> nextPeer_C[self], type |-> "LiftCommitJSON"])}}
                    ELSE /\ messages' = UNION{messages, {([liftId |-> liftId_Co[self], from |-> to_Co[self], to |-> nextPeer_C[self], type |-> "LiftCommitJSON"])}}
                         /\ UNCHANGED << lostMessages, printBuffer >>
              /\ pc' = [pc EXCEPT ![self] = "CL3_"]
              /\ UNCHANGED << Users, LiftProposers, ReliableUsers, Links, 
                              Cycles, tallies, readMessages, lifts, 
                              startedNodes, nextLiftGuid, stack, proposer, 
                              cycle, liftValue_P, arbitrator_P, nextPeer_, 
                              liftGuid, from_, to_, route_, liftValue_H, 
                              originator_, liftId_, arbitrator_H, prevPeer_, 
                              from_D, to_D, route_D, liftValue_D, originator_D, 
                              liftId_D, arbitrator_D, result_, from_C, to_C, 
                              route, liftValue, originator, liftId_C, 
                              arbitrator_C, result_C, to_R, liftId_R, result_R, 
                              prevPeer_R, timeout_, to_Re, liftId_Re, result, 
                              prevPeer, timeout, from_Co, to_Co, liftId_Co, 
                              nextPeer_C, liftValue_C, from_F, to, liftId_F, 
                              nextPeer, liftValue_F, from, liftId, arbitrator, 
                              cycle_, liftValue_, arbitrator_, toAct, lostMes >>

CL3_(self) == /\ pc[self] = "CL3_"
              /\ tallies' = [tallies EXCEPT ![<<to_Co[self], nextPeer_C[self], "Foil">>].balance = tallies[<<to_Co[self], nextPeer_C[self], "Foil">>].balance + liftValue_C[self]]
              /\ pc' = [pc EXCEPT ![self] = "CLR_"]
              /\ UNCHANGED << Users, LiftProposers, ReliableUsers, Links, 
                              Cycles, messages, readMessages, lostMessages, 
                              lifts, startedNodes, nextLiftGuid, stack, 
                              proposer, cycle, liftValue_P, arbitrator_P, 
                              nextPeer_, liftGuid, from_, to_, route_, 
                              liftValue_H, originator_, liftId_, arbitrator_H, 
                              prevPeer_, from_D, to_D, route_D, liftValue_D, 
                              originator_D, liftId_D, arbitrator_D, result_, 
                              from_C, to_C, route, liftValue, originator, 
                              liftId_C, arbitrator_C, result_C, to_R, liftId_R, 
                              result_R, prevPeer_R, timeout_, to_Re, liftId_Re, 
                              result, prevPeer, timeout, from_Co, to_Co, 
                              liftId_Co, nextPeer_C, liftValue_C, from_F, to, 
                              liftId_F, nextPeer, liftValue_F, from, liftId, 
                              arbitrator, cycle_, liftValue_, arbitrator_, 
                              toAct, lostMes, printBuffer >>

CLR_(self) == /\ pc[self] = "CLR_"
              /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
              /\ nextPeer_C' = [nextPeer_C EXCEPT ![self] = Head(stack[self]).nextPeer_C]
              /\ liftValue_C' = [liftValue_C EXCEPT ![self] = Head(stack[self]).liftValue_C]
              /\ from_Co' = [from_Co EXCEPT ![self] = Head(stack[self]).from_Co]
              /\ to_Co' = [to_Co EXCEPT ![self] = Head(stack[self]).to_Co]
              /\ liftId_Co' = [liftId_Co EXCEPT ![self] = Head(stack[self]).liftId_Co]
              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
              /\ UNCHANGED << Users, LiftProposers, ReliableUsers, Links, 
                              Cycles, tallies, messages, readMessages, 
                              lostMessages, lifts, startedNodes, nextLiftGuid, 
                              proposer, cycle, liftValue_P, arbitrator_P, 
                              nextPeer_, liftGuid, from_, to_, route_, 
                              liftValue_H, originator_, liftId_, arbitrator_H, 
                              prevPeer_, from_D, to_D, route_D, liftValue_D, 
                              originator_D, liftId_D, arbitrator_D, result_, 
                              from_C, to_C, route, liftValue, originator, 
                              liftId_C, arbitrator_C, result_C, to_R, liftId_R, 
                              result_R, prevPeer_R, timeout_, to_Re, liftId_Re, 
                              result, prevPeer, timeout, from_F, to, liftId_F, 
                              nextPeer, liftValue_F, from, liftId, arbitrator, 
                              cycle_, liftValue_, arbitrator_, toAct, lostMes, 
                              printBuffer >>

CommitLift(self) == CommitLift_(self) \/ CL2_(self) \/ CL4_(self)
                       \/ CL3_(self) \/ CLR_(self)

FailLift_(self) == /\ pc[self] = "FailLift_"
                   /\ printBuffer' = [printBuffer EXCEPT ![self] = Append(printBuffer[self], "Fail Lift")]
                   /\ IF liftId_F[self] \in DOMAIN lifts[to[self]]
                         THEN /\ liftValue_F' = [liftValue_F EXCEPT ![self] = lifts[to[self]][liftId_F[self]].value]
                              /\ lifts' = [lifts EXCEPT ![to[self]][liftId_F[self]].state = "Fail"]
                              /\ pc' = [pc EXCEPT ![self] = "CL2"]
                         ELSE /\ pc' = [pc EXCEPT ![self] = "CLR"]
                              /\ UNCHANGED << lifts, liftValue_F >>
                   /\ UNCHANGED << Users, LiftProposers, ReliableUsers, Links, 
                                   Cycles, tallies, messages, readMessages, 
                                   lostMessages, startedNodes, nextLiftGuid, 
                                   stack, proposer, cycle, liftValue_P, 
                                   arbitrator_P, nextPeer_, liftGuid, from_, 
                                   to_, route_, liftValue_H, originator_, 
                                   liftId_, arbitrator_H, prevPeer_, from_D, 
                                   to_D, route_D, liftValue_D, originator_D, 
                                   liftId_D, arbitrator_D, result_, from_C, 
                                   to_C, route, liftValue, originator, 
                                   liftId_C, arbitrator_C, result_C, to_R, 
                                   liftId_R, result_R, prevPeer_R, timeout_, 
                                   to_Re, liftId_Re, result, prevPeer, timeout, 
                                   from_Co, to_Co, liftId_Co, nextPeer_C, 
                                   liftValue_C, from_F, to, liftId_F, nextPeer, 
                                   from, liftId, arbitrator, cycle_, 
                                   liftValue_, arbitrator_, toAct, lostMes >>

CL2(self) == /\ pc[self] = "CL2"
             /\ tallies' = [tallies EXCEPT ![<<to[self], from_F[self], "Stock">>].projectedBalance = tallies[<<to[self], from_F[self], "Stock">>].projectedBalance + liftValue_F[self]]
             /\ IF to[self] /= lifts[to[self]][liftId_F[self]].originator
                   THEN /\ nextPeer' = [nextPeer EXCEPT ![self] = NextElemIn(to[self], lifts[to[self]][liftId_F[self]].route)]
                        /\ pc' = [pc EXCEPT ![self] = "CL4"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "CLR"]
                        /\ UNCHANGED nextPeer
             /\ UNCHANGED << Users, LiftProposers, ReliableUsers, Links, 
                             Cycles, messages, readMessages, lostMessages, 
                             lifts, startedNodes, nextLiftGuid, stack, 
                             proposer, cycle, liftValue_P, arbitrator_P, 
                             nextPeer_, liftGuid, from_, to_, route_, 
                             liftValue_H, originator_, liftId_, arbitrator_H, 
                             prevPeer_, from_D, to_D, route_D, liftValue_D, 
                             originator_D, liftId_D, arbitrator_D, result_, 
                             from_C, to_C, route, liftValue, originator, 
                             liftId_C, arbitrator_C, result_C, to_R, liftId_R, 
                             result_R, prevPeer_R, timeout_, to_Re, liftId_Re, 
                             result, prevPeer, timeout, from_Co, to_Co, 
                             liftId_Co, nextPeer_C, liftValue_C, from_F, to, 
                             liftId_F, liftValue_F, from, liftId, arbitrator, 
                             cycle_, liftValue_, arbitrator_, toAct, lostMes, 
                             printBuffer >>

CL4(self) == /\ pc[self] = "CL4"
             /\ IF MESSAGES_FAIL
                   THEN /\ \E messageWorks \in {TRUE, FALSE}:
                             IF messageWorks \/ ([liftId |-> liftId_F[self], from |-> to[self], to |-> nextPeer[self], type |-> "LiftFailJSON"]).to \in ReliableUsers \/ ([liftId |-> liftId_F[self], from |-> to[self], to |-> nextPeer[self], type |-> "LiftFailJSON"]).from \in ReliableUsers
                                THEN /\ messages' = UNION{messages, {([liftId |-> liftId_F[self], from |-> to[self], to |-> nextPeer[self], type |-> "LiftFailJSON"])}}
                                     /\ UNCHANGED << lostMessages, printBuffer >>
                                ELSE /\ printBuffer' = [printBuffer EXCEPT ![self] = Append(printBuffer[self], "Message Failed")]
                                     /\ messages' = UNION{messages, {([liftId |-> liftId_F[self], from |-> to[self], to |-> nextPeer[self], type |-> "LiftFailJSON"])}}
                                     /\ lostMessages' = UNION{lostMessages, {([liftId |-> liftId_F[self], from |-> to[self], to |-> nextPeer[self], type |-> "LiftFailJSON"])}}
                   ELSE /\ messages' = UNION{messages, {([liftId |-> liftId_F[self], from |-> to[self], to |-> nextPeer[self], type |-> "LiftFailJSON"])}}
                        /\ UNCHANGED << lostMessages, printBuffer >>
             /\ pc' = [pc EXCEPT ![self] = "CL3"]
             /\ UNCHANGED << Users, LiftProposers, ReliableUsers, Links, 
                             Cycles, tallies, readMessages, lifts, 
                             startedNodes, nextLiftGuid, stack, proposer, 
                             cycle, liftValue_P, arbitrator_P, nextPeer_, 
                             liftGuid, from_, to_, route_, liftValue_H, 
                             originator_, liftId_, arbitrator_H, prevPeer_, 
                             from_D, to_D, route_D, liftValue_D, originator_D, 
                             liftId_D, arbitrator_D, result_, from_C, to_C, 
                             route, liftValue, originator, liftId_C, 
                             arbitrator_C, result_C, to_R, liftId_R, result_R, 
                             prevPeer_R, timeout_, to_Re, liftId_Re, result, 
                             prevPeer, timeout, from_Co, to_Co, liftId_Co, 
                             nextPeer_C, liftValue_C, from_F, to, liftId_F, 
                             nextPeer, liftValue_F, from, liftId, arbitrator, 
                             cycle_, liftValue_, arbitrator_, toAct, lostMes >>

CL3(self) == /\ pc[self] = "CL3"
             /\ tallies' = [tallies EXCEPT ![<<to[self], nextPeer[self], "Foil">>].projectedBalance = tallies[<<to[self], nextPeer[self], "Foil">>].projectedBalance - liftValue_F[self]]
             /\ pc' = [pc EXCEPT ![self] = "CLR"]
             /\ UNCHANGED << Users, LiftProposers, ReliableUsers, Links, 
                             Cycles, messages, readMessages, lostMessages, 
                             lifts, startedNodes, nextLiftGuid, stack, 
                             proposer, cycle, liftValue_P, arbitrator_P, 
                             nextPeer_, liftGuid, from_, to_, route_, 
                             liftValue_H, originator_, liftId_, arbitrator_H, 
                             prevPeer_, from_D, to_D, route_D, liftValue_D, 
                             originator_D, liftId_D, arbitrator_D, result_, 
                             from_C, to_C, route, liftValue, originator, 
                             liftId_C, arbitrator_C, result_C, to_R, liftId_R, 
                             result_R, prevPeer_R, timeout_, to_Re, liftId_Re, 
                             result, prevPeer, timeout, from_Co, to_Co, 
                             liftId_Co, nextPeer_C, liftValue_C, from_F, to, 
                             liftId_F, nextPeer, liftValue_F, from, liftId, 
                             arbitrator, cycle_, liftValue_, arbitrator_, 
                             toAct, lostMes, printBuffer >>

CLR(self) == /\ pc[self] = "CLR"
             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
             /\ nextPeer' = [nextPeer EXCEPT ![self] = Head(stack[self]).nextPeer]
             /\ liftValue_F' = [liftValue_F EXCEPT ![self] = Head(stack[self]).liftValue_F]
             /\ from_F' = [from_F EXCEPT ![self] = Head(stack[self]).from_F]
             /\ to' = [to EXCEPT ![self] = Head(stack[self]).to]
             /\ liftId_F' = [liftId_F EXCEPT ![self] = Head(stack[self]).liftId_F]
             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
             /\ UNCHANGED << Users, LiftProposers, ReliableUsers, Links, 
                             Cycles, tallies, messages, readMessages, 
                             lostMessages, lifts, startedNodes, nextLiftGuid, 
                             proposer, cycle, liftValue_P, arbitrator_P, 
                             nextPeer_, liftGuid, from_, to_, route_, 
                             liftValue_H, originator_, liftId_, arbitrator_H, 
                             prevPeer_, from_D, to_D, route_D, liftValue_D, 
                             originator_D, liftId_D, arbitrator_D, result_, 
                             from_C, to_C, route, liftValue, originator, 
                             liftId_C, arbitrator_C, result_C, to_R, liftId_R, 
                             result_R, prevPeer_R, timeout_, to_Re, liftId_Re, 
                             result, prevPeer, timeout, from_Co, to_Co, 
                             liftId_Co, nextPeer_C, liftValue_C, from, liftId, 
                             arbitrator, cycle_, liftValue_, arbitrator_, 
                             toAct, lostMes, printBuffer >>

FailLift(self) == FailLift_(self) \/ CL2(self) \/ CL4(self) \/ CL3(self)
                     \/ CLR(self)

CheckTimeout_(self) == /\ pc[self] = "CheckTimeout_"
                       /\ printBuffer' = [printBuffer EXCEPT ![self] = Append(printBuffer[self], "Check Timeout")]
                       /\ pc' = [pc EXCEPT ![self] = "losm"]
                       /\ UNCHANGED << Users, LiftProposers, ReliableUsers, 
                                       Links, Cycles, tallies, messages, 
                                       readMessages, lostMessages, lifts, 
                                       startedNodes, nextLiftGuid, stack, 
                                       proposer, cycle, liftValue_P, 
                                       arbitrator_P, nextPeer_, liftGuid, 
                                       from_, to_, route_, liftValue_H, 
                                       originator_, liftId_, arbitrator_H, 
                                       prevPeer_, from_D, to_D, route_D, 
                                       liftValue_D, originator_D, liftId_D, 
                                       arbitrator_D, result_, from_C, to_C, 
                                       route, liftValue, originator, liftId_C, 
                                       arbitrator_C, result_C, to_R, liftId_R, 
                                       result_R, prevPeer_R, timeout_, to_Re, 
                                       liftId_Re, result, prevPeer, timeout, 
                                       from_Co, to_Co, liftId_Co, nextPeer_C, 
                                       liftValue_C, from_F, to, liftId_F, 
                                       nextPeer, liftValue_F, from, liftId, 
                                       arbitrator, cycle_, liftValue_, 
                                       arbitrator_, toAct, lostMes >>

losm(self) == /\ pc[self] = "losm"
              /\ IF MESSAGES_FAIL
                    THEN /\ \E messageWorks \in {TRUE, FALSE}:
                              IF messageWorks \/ ([liftId |-> liftId[self], originator |-> originator[self], from |-> from[self], to |-> arbitrator[self], type |-> "LiftCheckJSON", route |-> lifts[from[self]][liftId[self]].route, value |-> lifts[from[self]][liftId[self]].value, arbitrator |-> arbitrator[self]]).to \in ReliableUsers \/ ([liftId |-> liftId[self], originator |-> originator[self], from |-> from[self], to |-> arbitrator[self], type |-> "LiftCheckJSON", route |-> lifts[from[self]][liftId[self]].route, value |-> lifts[from[self]][liftId[self]].value, arbitrator |-> arbitrator[self]]).from \in ReliableUsers
                                 THEN /\ messages' = UNION{messages, {([liftId |-> liftId[self], originator |-> originator[self], from |-> from[self], to |-> arbitrator[self], type |-> "LiftCheckJSON", route |-> lifts[from[self]][liftId[self]].route, value |-> lifts[from[self]][liftId[self]].value, arbitrator |-> arbitrator[self]])}}
                                      /\ UNCHANGED << lostMessages, 
                                                      printBuffer >>
                                 ELSE /\ printBuffer' = [printBuffer EXCEPT ![self] = Append(printBuffer[self], "Message Failed")]
                                      /\ messages' = UNION{messages, {([liftId |-> liftId[self], originator |-> originator[self], from |-> from[self], to |-> arbitrator[self], type |-> "LiftCheckJSON", route |-> lifts[from[self]][liftId[self]].route, value |-> lifts[from[self]][liftId[self]].value, arbitrator |-> arbitrator[self]])}}
                                      /\ lostMessages' = UNION{lostMessages, {([liftId |-> liftId[self], originator |-> originator[self], from |-> from[self], to |-> arbitrator[self], type |-> "LiftCheckJSON", route |-> lifts[from[self]][liftId[self]].route, value |-> lifts[from[self]][liftId[self]].value, arbitrator |-> arbitrator[self]])}}
                    ELSE /\ messages' = UNION{messages, {([liftId |-> liftId[self], originator |-> originator[self], from |-> from[self], to |-> arbitrator[self], type |-> "LiftCheckJSON", route |-> lifts[from[self]][liftId[self]].route, value |-> lifts[from[self]][liftId[self]].value, arbitrator |-> arbitrator[self]])}}
                         /\ UNCHANGED << lostMessages, printBuffer >>
              /\ pc' = [pc EXCEPT ![self] = "CTR"]
              /\ UNCHANGED << Users, LiftProposers, ReliableUsers, Links, 
                              Cycles, tallies, readMessages, lifts, 
                              startedNodes, nextLiftGuid, stack, proposer, 
                              cycle, liftValue_P, arbitrator_P, nextPeer_, 
                              liftGuid, from_, to_, route_, liftValue_H, 
                              originator_, liftId_, arbitrator_H, prevPeer_, 
                              from_D, to_D, route_D, liftValue_D, originator_D, 
                              liftId_D, arbitrator_D, result_, from_C, to_C, 
                              route, liftValue, originator, liftId_C, 
                              arbitrator_C, result_C, to_R, liftId_R, result_R, 
                              prevPeer_R, timeout_, to_Re, liftId_Re, result, 
                              prevPeer, timeout, from_Co, to_Co, liftId_Co, 
                              nextPeer_C, liftValue_C, from_F, to, liftId_F, 
                              nextPeer, liftValue_F, from, liftId, arbitrator, 
                              cycle_, liftValue_, arbitrator_, toAct, lostMes >>

CTR(self) == /\ pc[self] = "CTR"
             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
             /\ from' = [from EXCEPT ![self] = Head(stack[self]).from]
             /\ liftId' = [liftId EXCEPT ![self] = Head(stack[self]).liftId]
             /\ arbitrator' = [arbitrator EXCEPT ![self] = Head(stack[self]).arbitrator]
             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
             /\ UNCHANGED << Users, LiftProposers, ReliableUsers, Links, 
                             Cycles, tallies, messages, readMessages, 
                             lostMessages, lifts, startedNodes, nextLiftGuid, 
                             proposer, cycle, liftValue_P, arbitrator_P, 
                             nextPeer_, liftGuid, from_, to_, route_, 
                             liftValue_H, originator_, liftId_, arbitrator_H, 
                             prevPeer_, from_D, to_D, route_D, liftValue_D, 
                             originator_D, liftId_D, arbitrator_D, result_, 
                             from_C, to_C, route, liftValue, originator, 
                             liftId_C, arbitrator_C, result_C, to_R, liftId_R, 
                             result_R, prevPeer_R, timeout_, to_Re, liftId_Re, 
                             result, prevPeer, timeout, from_Co, to_Co, 
                             liftId_Co, nextPeer_C, liftValue_C, from_F, to, 
                             liftId_F, nextPeer, liftValue_F, cycle_, 
                             liftValue_, arbitrator_, toAct, lostMes, 
                             printBuffer >>

CheckTimeout(self) == CheckTimeout_(self) \/ losm(self) \/ CTR(self)

ProcStart(self) == /\ pc[self] = "ProcStart"
                   /\ printBuffer' = [printBuffer EXCEPT ![self] = Append(printBuffer[self], "Start")]
                   /\ pc' = [pc EXCEPT ![self] = "l1"]
                   /\ UNCHANGED << Users, LiftProposers, ReliableUsers, Links, 
                                   Cycles, tallies, messages, readMessages, 
                                   lostMessages, lifts, startedNodes, 
                                   nextLiftGuid, stack, proposer, cycle, 
                                   liftValue_P, arbitrator_P, nextPeer_, 
                                   liftGuid, from_, to_, route_, liftValue_H, 
                                   originator_, liftId_, arbitrator_H, 
                                   prevPeer_, from_D, to_D, route_D, 
                                   liftValue_D, originator_D, liftId_D, 
                                   arbitrator_D, result_, from_C, to_C, route, 
                                   liftValue, originator, liftId_C, 
                                   arbitrator_C, result_C, to_R, liftId_R, 
                                   result_R, prevPeer_R, timeout_, to_Re, 
                                   liftId_Re, result, prevPeer, timeout, 
                                   from_Co, to_Co, liftId_Co, nextPeer_C, 
                                   liftValue_C, from_F, to, liftId_F, nextPeer, 
                                   liftValue_F, from, liftId, arbitrator, 
                                   cycle_, liftValue_, arbitrator_, toAct, 
                                   lostMes >>

l1(self) == /\ pc[self] = "l1"
            /\ printBuffer' = [printBuffer EXCEPT ![self] = Append(printBuffer[self], self)]
            /\ IF self \in LiftProposers
                  THEN /\ cycle_' = [cycle_ EXCEPT ![self] = CHOOSE c \in Cycles : c[1] = self]
                       /\ liftValue_' = [liftValue_ EXCEPT ![self] = MaxLiftValueFor(cycle_'[self], tallies)]
                       /\ arbitrator_' = [arbitrator_ EXCEPT ![self] = CHOOSE a \in ReliableUsers : TRUE]
                       /\ /\ arbitrator_P' = [arbitrator_P EXCEPT ![self] = arbitrator_'[self]]
                          /\ cycle' = [cycle EXCEPT ![self] = cycle_'[self]]
                          /\ liftValue_P' = [liftValue_P EXCEPT ![self] = liftValue_'[self]]
                          /\ proposer' = [proposer EXCEPT ![self] = self]
                          /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "ProposeLift",
                                                                   pc        |->  "lsn",
                                                                   nextPeer_ |->  nextPeer_[self],
                                                                   liftGuid  |->  liftGuid[self],
                                                                   proposer  |->  proposer[self],
                                                                   cycle     |->  cycle[self],
                                                                   liftValue_P |->  liftValue_P[self],
                                                                   arbitrator_P |->  arbitrator_P[self] ] >>
                                                               \o stack[self]]
                       /\ nextPeer_' = [nextPeer_ EXCEPT ![self] = defaultInitValue]
                       /\ liftGuid' = [liftGuid EXCEPT ![self] = defaultInitValue]
                       /\ pc' = [pc EXCEPT ![self] = "ProposeLift_"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "lsn"]
                       /\ UNCHANGED << stack, proposer, cycle, liftValue_P, 
                                       arbitrator_P, nextPeer_, liftGuid, 
                                       cycle_, liftValue_, arbitrator_ >>
            /\ UNCHANGED << Users, LiftProposers, ReliableUsers, Links, Cycles, 
                            tallies, messages, readMessages, lostMessages, 
                            lifts, startedNodes, nextLiftGuid, from_, to_, 
                            route_, liftValue_H, originator_, liftId_, 
                            arbitrator_H, prevPeer_, from_D, to_D, route_D, 
                            liftValue_D, originator_D, liftId_D, arbitrator_D, 
                            result_, from_C, to_C, route, liftValue, 
                            originator, liftId_C, arbitrator_C, result_C, to_R, 
                            liftId_R, result_R, prevPeer_R, timeout_, to_Re, 
                            liftId_Re, result, prevPeer, timeout, from_Co, 
                            to_Co, liftId_Co, nextPeer_C, liftValue_C, from_F, 
                            to, liftId_F, nextPeer, liftValue_F, from, liftId, 
                            arbitrator, toAct, lostMes >>

lsn(self) == /\ pc[self] = "lsn"
             /\ startedNodes' = UNION{startedNodes, {self}}
             /\ pc' = [pc EXCEPT ![self] = "las"]
             /\ UNCHANGED << Users, LiftProposers, ReliableUsers, Links, 
                             Cycles, tallies, messages, readMessages, 
                             lostMessages, lifts, nextLiftGuid, stack, 
                             proposer, cycle, liftValue_P, arbitrator_P, 
                             nextPeer_, liftGuid, from_, to_, route_, 
                             liftValue_H, originator_, liftId_, arbitrator_H, 
                             prevPeer_, from_D, to_D, route_D, liftValue_D, 
                             originator_D, liftId_D, arbitrator_D, result_, 
                             from_C, to_C, route, liftValue, originator, 
                             liftId_C, arbitrator_C, result_C, to_R, liftId_R, 
                             result_R, prevPeer_R, timeout_, to_Re, liftId_Re, 
                             result, prevPeer, timeout, from_Co, to_Co, 
                             liftId_Co, nextPeer_C, liftValue_C, from_F, to, 
                             liftId_F, nextPeer, liftValue_F, from, liftId, 
                             arbitrator, cycle_, liftValue_, arbitrator_, 
                             toAct, lostMes, printBuffer >>

las(self) == /\ pc[self] = "las"
             /\ startedNodes = Users
             /\ pc' = [pc EXCEPT ![self] = "l2w"]
             /\ UNCHANGED << Users, LiftProposers, ReliableUsers, Links, 
                             Cycles, tallies, messages, readMessages, 
                             lostMessages, lifts, startedNodes, nextLiftGuid, 
                             stack, proposer, cycle, liftValue_P, arbitrator_P, 
                             nextPeer_, liftGuid, from_, to_, route_, 
                             liftValue_H, originator_, liftId_, arbitrator_H, 
                             prevPeer_, from_D, to_D, route_D, liftValue_D, 
                             originator_D, liftId_D, arbitrator_D, result_, 
                             from_C, to_C, route, liftValue, originator, 
                             liftId_C, arbitrator_C, result_C, to_R, liftId_R, 
                             result_R, prevPeer_R, timeout_, to_Re, liftId_Re, 
                             result, prevPeer, timeout, from_Co, to_Co, 
                             liftId_Co, nextPeer_C, liftValue_C, from_F, to, 
                             liftId_F, nextPeer, liftValue_F, from, liftId, 
                             arbitrator, cycle_, liftValue_, arbitrator_, 
                             toAct, lostMes, printBuffer >>

l2w(self) == /\ pc[self] = "l2w"
             /\ IF NotDone(lifts, Users, messages, UNION{readMessages, lostMessages})
                   THEN /\ IF (\E message \in messages: message \notin UNION{readMessages, lostMessages} /\ message.to = self)
                              THEN /\ IF messages \ UNION{readMessages,lostMessages} /= {}
                                         THEN /\ toAct' = [toAct EXCEPT ![self] = CHOOSE message \in messages: message \notin UNION{readMessages,lostMessages} /\ message.to = self]
                                              /\ IF toAct'[self].type = "LiftProposeJSON"
                                                    THEN /\ /\ arbitrator_H' = [arbitrator_H EXCEPT ![self] = toAct'[self].arbitrator]
                                                            /\ from_' = [from_ EXCEPT ![self] = toAct'[self].from]
                                                            /\ liftId_' = [liftId_ EXCEPT ![self] = toAct'[self].liftId]
                                                            /\ liftValue_H' = [liftValue_H EXCEPT ![self] = toAct'[self].value]
                                                            /\ originator_' = [originator_ EXCEPT ![self] = toAct'[self].originator]
                                                            /\ route_' = [route_ EXCEPT ![self] = toAct'[self].route]
                                                            /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "HandleLift",
                                                                                                     pc        |->  "l5",
                                                                                                     prevPeer_ |->  prevPeer_[self],
                                                                                                     from_     |->  from_[self],
                                                                                                     to_       |->  to_[self],
                                                                                                     route_    |->  route_[self],
                                                                                                     liftValue_H |->  liftValue_H[self],
                                                                                                     originator_ |->  originator_[self],
                                                                                                     liftId_   |->  liftId_[self],
                                                                                                     arbitrator_H |->  arbitrator_H[self] ] >>
                                                                                                 \o stack[self]]
                                                            /\ to_' = [to_ EXCEPT ![self] = toAct'[self].to]
                                                         /\ prevPeer_' = [prevPeer_ EXCEPT ![self] = defaultInitValue]
                                                         /\ pc' = [pc EXCEPT ![self] = "HandleLift_"]
                                                    ELSE /\ pc' = [pc EXCEPT ![self] = "l5"]
                                                         /\ UNCHANGED << stack, 
                                                                         from_, 
                                                                         to_, 
                                                                         route_, 
                                                                         liftValue_H, 
                                                                         originator_, 
                                                                         liftId_, 
                                                                         arbitrator_H, 
                                                                         prevPeer_ >>
                                         ELSE /\ pc' = [pc EXCEPT ![self] = "l2w"]
                                              /\ UNCHANGED << stack, from_, 
                                                              to_, route_, 
                                                              liftValue_H, 
                                                              originator_, 
                                                              liftId_, 
                                                              arbitrator_H, 
                                                              prevPeer_, toAct >>
                              ELSE /\ IF \E message \in lostMessages : message \notin readMessages /\ message.to = self
                                         THEN /\ pc' = [pc EXCEPT ![self] = "clm"]
                                         ELSE /\ pc' = [pc EXCEPT ![self] = "l2w"]
                                   /\ UNCHANGED << stack, from_, to_, route_, 
                                                   liftValue_H, originator_, 
                                                   liftId_, arbitrator_H, 
                                                   prevPeer_, toAct >>
                   ELSE /\ pc' = [pc EXCEPT ![self] = "lpb"]
                        /\ UNCHANGED << stack, from_, to_, route_, liftValue_H, 
                                        originator_, liftId_, arbitrator_H, 
                                        prevPeer_, toAct >>
             /\ UNCHANGED << Users, LiftProposers, ReliableUsers, Links, 
                             Cycles, tallies, messages, readMessages, 
                             lostMessages, lifts, startedNodes, nextLiftGuid, 
                             proposer, cycle, liftValue_P, arbitrator_P, 
                             nextPeer_, liftGuid, from_D, to_D, route_D, 
                             liftValue_D, originator_D, liftId_D, arbitrator_D, 
                             result_, from_C, to_C, route, liftValue, 
                             originator, liftId_C, arbitrator_C, result_C, 
                             to_R, liftId_R, result_R, prevPeer_R, timeout_, 
                             to_Re, liftId_Re, result, prevPeer, timeout, 
                             from_Co, to_Co, liftId_Co, nextPeer_C, 
                             liftValue_C, from_F, to, liftId_F, nextPeer, 
                             liftValue_F, from, liftId, arbitrator, cycle_, 
                             liftValue_, arbitrator_, lostMes, printBuffer >>

l5(self) == /\ pc[self] = "l5"
            /\ IF toAct[self].type = "LiftCommitJSON"
                  THEN /\ /\ from_Co' = [from_Co EXCEPT ![self] = toAct[self].from]
                          /\ liftId_Co' = [liftId_Co EXCEPT ![self] = toAct[self].liftId]
                          /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "CommitLift",
                                                                   pc        |->  "l6",
                                                                   nextPeer_C |->  nextPeer_C[self],
                                                                   liftValue_C |->  liftValue_C[self],
                                                                   from_Co   |->  from_Co[self],
                                                                   to_Co     |->  to_Co[self],
                                                                   liftId_Co |->  liftId_Co[self] ] >>
                                                               \o stack[self]]
                          /\ to_Co' = [to_Co EXCEPT ![self] = toAct[self].to]
                       /\ nextPeer_C' = [nextPeer_C EXCEPT ![self] = defaultInitValue]
                       /\ liftValue_C' = [liftValue_C EXCEPT ![self] = defaultInitValue]
                       /\ pc' = [pc EXCEPT ![self] = "CommitLift_"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "l6"]
                       /\ UNCHANGED << stack, from_Co, to_Co, liftId_Co, 
                                       nextPeer_C, liftValue_C >>
            /\ UNCHANGED << Users, LiftProposers, ReliableUsers, Links, Cycles, 
                            tallies, messages, readMessages, lostMessages, 
                            lifts, startedNodes, nextLiftGuid, proposer, cycle, 
                            liftValue_P, arbitrator_P, nextPeer_, liftGuid, 
                            from_, to_, route_, liftValue_H, originator_, 
                            liftId_, arbitrator_H, prevPeer_, from_D, to_D, 
                            route_D, liftValue_D, originator_D, liftId_D, 
                            arbitrator_D, result_, from_C, to_C, route, 
                            liftValue, originator, liftId_C, arbitrator_C, 
                            result_C, to_R, liftId_R, result_R, prevPeer_R, 
                            timeout_, to_Re, liftId_Re, result, prevPeer, 
                            timeout, from_F, to, liftId_F, nextPeer, 
                            liftValue_F, from, liftId, arbitrator, cycle_, 
                            liftValue_, arbitrator_, toAct, lostMes, 
                            printBuffer >>

l6(self) == /\ pc[self] = "l6"
            /\ IF toAct[self].type = "LiftFailJSON"
                  THEN /\ /\ from_F' = [from_F EXCEPT ![self] = toAct[self].from]
                          /\ liftId_F' = [liftId_F EXCEPT ![self] = toAct[self].liftId]
                          /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "FailLift",
                                                                   pc        |->  "l7",
                                                                   nextPeer  |->  nextPeer[self],
                                                                   liftValue_F |->  liftValue_F[self],
                                                                   from_F    |->  from_F[self],
                                                                   to        |->  to[self],
                                                                   liftId_F  |->  liftId_F[self] ] >>
                                                               \o stack[self]]
                          /\ to' = [to EXCEPT ![self] = toAct[self].to]
                       /\ nextPeer' = [nextPeer EXCEPT ![self] = defaultInitValue]
                       /\ liftValue_F' = [liftValue_F EXCEPT ![self] = defaultInitValue]
                       /\ pc' = [pc EXCEPT ![self] = "FailLift_"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "l7"]
                       /\ UNCHANGED << stack, from_F, to, liftId_F, nextPeer, 
                                       liftValue_F >>
            /\ UNCHANGED << Users, LiftProposers, ReliableUsers, Links, Cycles, 
                            tallies, messages, readMessages, lostMessages, 
                            lifts, startedNodes, nextLiftGuid, proposer, cycle, 
                            liftValue_P, arbitrator_P, nextPeer_, liftGuid, 
                            from_, to_, route_, liftValue_H, originator_, 
                            liftId_, arbitrator_H, prevPeer_, from_D, to_D, 
                            route_D, liftValue_D, originator_D, liftId_D, 
                            arbitrator_D, result_, from_C, to_C, route, 
                            liftValue, originator, liftId_C, arbitrator_C, 
                            result_C, to_R, liftId_R, result_R, prevPeer_R, 
                            timeout_, to_Re, liftId_Re, result, prevPeer, 
                            timeout, from_Co, to_Co, liftId_Co, nextPeer_C, 
                            liftValue_C, from, liftId, arbitrator, cycle_, 
                            liftValue_, arbitrator_, toAct, lostMes, 
                            printBuffer >>

l7(self) == /\ pc[self] = "l7"
            /\ IF toAct[self].type = "LiftValidateJSON"
                  THEN /\ /\ arbitrator_D' = [arbitrator_D EXCEPT ![self] = toAct[self].arbitrator]
                          /\ from_D' = [from_D EXCEPT ![self] = toAct[self].from]
                          /\ liftId_D' = [liftId_D EXCEPT ![self] = toAct[self].liftId]
                          /\ liftValue_D' = [liftValue_D EXCEPT ![self] = toAct[self].value]
                          /\ originator_D' = [originator_D EXCEPT ![self] = toAct[self].originator]
                          /\ route_D' = [route_D EXCEPT ![self] = toAct[self].route]
                          /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "DecideLiftValidity",
                                                                   pc        |->  "l8",
                                                                   result_   |->  result_[self],
                                                                   from_D    |->  from_D[self],
                                                                   to_D      |->  to_D[self],
                                                                   route_D   |->  route_D[self],
                                                                   liftValue_D |->  liftValue_D[self],
                                                                   originator_D |->  originator_D[self],
                                                                   liftId_D  |->  liftId_D[self],
                                                                   arbitrator_D |->  arbitrator_D[self] ] >>
                                                               \o stack[self]]
                          /\ to_D' = [to_D EXCEPT ![self] = toAct[self].to]
                       /\ result_' = [result_ EXCEPT ![self] = defaultInitValue]
                       /\ pc' = [pc EXCEPT ![self] = "DecideLiftValidity_"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "l8"]
                       /\ UNCHANGED << stack, from_D, to_D, route_D, 
                                       liftValue_D, originator_D, liftId_D, 
                                       arbitrator_D, result_ >>
            /\ UNCHANGED << Users, LiftProposers, ReliableUsers, Links, Cycles, 
                            tallies, messages, readMessages, lostMessages, 
                            lifts, startedNodes, nextLiftGuid, proposer, cycle, 
                            liftValue_P, arbitrator_P, nextPeer_, liftGuid, 
                            from_, to_, route_, liftValue_H, originator_, 
                            liftId_, arbitrator_H, prevPeer_, from_C, to_C, 
                            route, liftValue, originator, liftId_C, 
                            arbitrator_C, result_C, to_R, liftId_R, result_R, 
                            prevPeer_R, timeout_, to_Re, liftId_Re, result, 
                            prevPeer, timeout, from_Co, to_Co, liftId_Co, 
                            nextPeer_C, liftValue_C, from_F, to, liftId_F, 
                            nextPeer, liftValue_F, from, liftId, arbitrator, 
                            cycle_, liftValue_, arbitrator_, toAct, lostMes, 
                            printBuffer >>

l8(self) == /\ pc[self] = "l8"
            /\ IF toAct[self].type = "LiftCheckJSON"
                  THEN /\ /\ arbitrator_C' = [arbitrator_C EXCEPT ![self] = toAct[self].arbitrator]
                          /\ from_C' = [from_C EXCEPT ![self] = toAct[self].from]
                          /\ liftId_C' = [liftId_C EXCEPT ![self] = toAct[self].liftId]
                          /\ liftValue' = [liftValue EXCEPT ![self] = toAct[self].value]
                          /\ originator' = [originator EXCEPT ![self] = toAct[self].originator]
                          /\ route' = [route EXCEPT ![self] = toAct[self].route]
                          /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "CheckLiftValidity",
                                                                   pc        |->  "l9",
                                                                   result_C  |->  result_C[self],
                                                                   from_C    |->  from_C[self],
                                                                   to_C      |->  to_C[self],
                                                                   route     |->  route[self],
                                                                   liftValue |->  liftValue[self],
                                                                   originator |->  originator[self],
                                                                   liftId_C  |->  liftId_C[self],
                                                                   arbitrator_C |->  arbitrator_C[self] ] >>
                                                               \o stack[self]]
                          /\ to_C' = [to_C EXCEPT ![self] = toAct[self].to]
                       /\ result_C' = [result_C EXCEPT ![self] = defaultInitValue]
                       /\ pc' = [pc EXCEPT ![self] = "CkeckLiftValidity"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "l9"]
                       /\ UNCHANGED << stack, from_C, to_C, route, liftValue, 
                                       originator, liftId_C, arbitrator_C, 
                                       result_C >>
            /\ UNCHANGED << Users, LiftProposers, ReliableUsers, Links, Cycles, 
                            tallies, messages, readMessages, lostMessages, 
                            lifts, startedNodes, nextLiftGuid, proposer, cycle, 
                            liftValue_P, arbitrator_P, nextPeer_, liftGuid, 
                            from_, to_, route_, liftValue_H, originator_, 
                            liftId_, arbitrator_H, prevPeer_, from_D, to_D, 
                            route_D, liftValue_D, originator_D, liftId_D, 
                            arbitrator_D, result_, to_R, liftId_R, result_R, 
                            prevPeer_R, timeout_, to_Re, liftId_Re, result, 
                            prevPeer, timeout, from_Co, to_Co, liftId_Co, 
                            nextPeer_C, liftValue_C, from_F, to, liftId_F, 
                            nextPeer, liftValue_F, from, liftId, arbitrator, 
                            cycle_, liftValue_, arbitrator_, toAct, lostMes, 
                            printBuffer >>

l9(self) == /\ pc[self] = "l9"
            /\ IF toAct[self].type = "LiftValidResultJSON"
                  THEN /\ /\ liftId_R' = [liftId_R EXCEPT ![self] = toAct[self].liftId]
                          /\ result_R' = [result_R EXCEPT ![self] = toAct[self].result]
                          /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "ReceiveLiftValidResult",
                                                                   pc        |->  "l10",
                                                                   prevPeer_R |->  prevPeer_R[self],
                                                                   timeout_  |->  timeout_[self],
                                                                   to_R      |->  to_R[self],
                                                                   liftId_R  |->  liftId_R[self],
                                                                   result_R  |->  result_R[self] ] >>
                                                               \o stack[self]]
                          /\ to_R' = [to_R EXCEPT ![self] = toAct[self].to]
                       /\ prevPeer_R' = [prevPeer_R EXCEPT ![self] = defaultInitValue]
                       /\ timeout_' = [timeout_ EXCEPT ![self] = defaultInitValue]
                       /\ pc' = [pc EXCEPT ![self] = "ValidateLift_"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "l10"]
                       /\ UNCHANGED << stack, to_R, liftId_R, result_R, 
                                       prevPeer_R, timeout_ >>
            /\ UNCHANGED << Users, LiftProposers, ReliableUsers, Links, Cycles, 
                            tallies, messages, readMessages, lostMessages, 
                            lifts, startedNodes, nextLiftGuid, proposer, cycle, 
                            liftValue_P, arbitrator_P, nextPeer_, liftGuid, 
                            from_, to_, route_, liftValue_H, originator_, 
                            liftId_, arbitrator_H, prevPeer_, from_D, to_D, 
                            route_D, liftValue_D, originator_D, liftId_D, 
                            arbitrator_D, result_, from_C, to_C, route, 
                            liftValue, originator, liftId_C, arbitrator_C, 
                            result_C, to_Re, liftId_Re, result, prevPeer, 
                            timeout, from_Co, to_Co, liftId_Co, nextPeer_C, 
                            liftValue_C, from_F, to, liftId_F, nextPeer, 
                            liftValue_F, from, liftId, arbitrator, cycle_, 
                            liftValue_, arbitrator_, toAct, lostMes, 
                            printBuffer >>

l10(self) == /\ pc[self] = "l10"
             /\ IF toAct[self].type = "LiftCheckResultJSON"
                   THEN /\ /\ liftId_Re' = [liftId_Re EXCEPT ![self] = toAct[self].liftId]
                           /\ result' = [result EXCEPT ![self] = toAct[self].result]
                           /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "ReceiveLiftCheckResult",
                                                                    pc        |->  "l4",
                                                                    prevPeer  |->  prevPeer[self],
                                                                    timeout   |->  timeout[self],
                                                                    to_Re     |->  to_Re[self],
                                                                    liftId_Re |->  liftId_Re[self],
                                                                    result    |->  result[self] ] >>
                                                                \o stack[self]]
                           /\ to_Re' = [to_Re EXCEPT ![self] = toAct[self].to]
                        /\ prevPeer' = [prevPeer EXCEPT ![self] = defaultInitValue]
                        /\ timeout' = [timeout EXCEPT ![self] = defaultInitValue]
                        /\ pc' = [pc EXCEPT ![self] = "ValidateLift"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "l4"]
                        /\ UNCHANGED << stack, to_Re, liftId_Re, result, 
                                        prevPeer, timeout >>
             /\ UNCHANGED << Users, LiftProposers, ReliableUsers, Links, 
                             Cycles, tallies, messages, readMessages, 
                             lostMessages, lifts, startedNodes, nextLiftGuid, 
                             proposer, cycle, liftValue_P, arbitrator_P, 
                             nextPeer_, liftGuid, from_, to_, route_, 
                             liftValue_H, originator_, liftId_, arbitrator_H, 
                             prevPeer_, from_D, to_D, route_D, liftValue_D, 
                             originator_D, liftId_D, arbitrator_D, result_, 
                             from_C, to_C, route, liftValue, originator, 
                             liftId_C, arbitrator_C, result_C, to_R, liftId_R, 
                             result_R, prevPeer_R, timeout_, from_Co, to_Co, 
                             liftId_Co, nextPeer_C, liftValue_C, from_F, to, 
                             liftId_F, nextPeer, liftValue_F, from, liftId, 
                             arbitrator, cycle_, liftValue_, arbitrator_, 
                             toAct, lostMes, printBuffer >>

l4(self) == /\ pc[self] = "l4"
            /\ readMessages' = UNION{readMessages, {toAct[self]}}
            /\ pc' = [pc EXCEPT ![self] = "l2w"]
            /\ UNCHANGED << Users, LiftProposers, ReliableUsers, Links, Cycles, 
                            tallies, messages, lostMessages, lifts, 
                            startedNodes, nextLiftGuid, stack, proposer, cycle, 
                            liftValue_P, arbitrator_P, nextPeer_, liftGuid, 
                            from_, to_, route_, liftValue_H, originator_, 
                            liftId_, arbitrator_H, prevPeer_, from_D, to_D, 
                            route_D, liftValue_D, originator_D, liftId_D, 
                            arbitrator_D, result_, from_C, to_C, route, 
                            liftValue, originator, liftId_C, arbitrator_C, 
                            result_C, to_R, liftId_R, result_R, prevPeer_R, 
                            timeout_, to_Re, liftId_Re, result, prevPeer, 
                            timeout, from_Co, to_Co, liftId_Co, nextPeer_C, 
                            liftValue_C, from_F, to, liftId_F, nextPeer, 
                            liftValue_F, from, liftId, arbitrator, cycle_, 
                            liftValue_, arbitrator_, toAct, lostMes, 
                            printBuffer >>

clm(self) == /\ pc[self] = "clm"
             /\ lostMes' = [lostMes EXCEPT ![self] = CHOOSE message \in lostMessages : message \notin readMessages /\ (message.to = self \/ message.from = self)]
             /\ pc' = [pc EXCEPT ![self] = "lcl"]
             /\ UNCHANGED << Users, LiftProposers, ReliableUsers, Links, 
                             Cycles, tallies, messages, readMessages, 
                             lostMessages, lifts, startedNodes, nextLiftGuid, 
                             stack, proposer, cycle, liftValue_P, arbitrator_P, 
                             nextPeer_, liftGuid, from_, to_, route_, 
                             liftValue_H, originator_, liftId_, arbitrator_H, 
                             prevPeer_, from_D, to_D, route_D, liftValue_D, 
                             originator_D, liftId_D, arbitrator_D, result_, 
                             from_C, to_C, route, liftValue, originator, 
                             liftId_C, arbitrator_C, result_C, to_R, liftId_R, 
                             result_R, prevPeer_R, timeout_, to_Re, liftId_Re, 
                             result, prevPeer, timeout, from_Co, to_Co, 
                             liftId_Co, nextPeer_C, liftValue_C, from_F, to, 
                             liftId_F, nextPeer, liftValue_F, from, liftId, 
                             arbitrator, cycle_, liftValue_, arbitrator_, 
                             toAct, printBuffer >>

lcl(self) == /\ pc[self] = "lcl"
             /\ IF (lostMes[self].type = "LiftCommitJSON" \/ lostMes[self].type = "LiftFailJSON") /\ lostMes[self].to = self
                   THEN /\ IF lostMes[self].liftId \in DOMAIN lifts[self] /\ lifts[self][lostMes[self].liftId].arbitrator /= self /\ lifts[self][lostMes[self].liftId].state = "Seek"
                              THEN /\ /\ arbitrator' = [arbitrator EXCEPT ![self] = lifts[self][lostMes[self].liftId].arbitrator]
                                      /\ from' = [from EXCEPT ![self] = self]
                                      /\ liftId' = [liftId EXCEPT ![self] = lostMes[self].liftId]
                                      /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "CheckTimeout",
                                                                               pc        |->  "lpl",
                                                                               from      |->  from[self],
                                                                               liftId    |->  liftId[self],
                                                                               arbitrator |->  arbitrator[self] ] >>
                                                                           \o stack[self]]
                                   /\ pc' = [pc EXCEPT ![self] = "CheckTimeout_"]
                              ELSE /\ pc' = [pc EXCEPT ![self] = "lpl"]
                                   /\ UNCHANGED << stack, from, liftId, 
                                                   arbitrator >>
                   ELSE /\ pc' = [pc EXCEPT ![self] = "lpl"]
                        /\ UNCHANGED << stack, from, liftId, arbitrator >>
             /\ UNCHANGED << Users, LiftProposers, ReliableUsers, Links, 
                             Cycles, tallies, messages, readMessages, 
                             lostMessages, lifts, startedNodes, nextLiftGuid, 
                             proposer, cycle, liftValue_P, arbitrator_P, 
                             nextPeer_, liftGuid, from_, to_, route_, 
                             liftValue_H, originator_, liftId_, arbitrator_H, 
                             prevPeer_, from_D, to_D, route_D, liftValue_D, 
                             originator_D, liftId_D, arbitrator_D, result_, 
                             from_C, to_C, route, liftValue, originator, 
                             liftId_C, arbitrator_C, result_C, to_R, liftId_R, 
                             result_R, prevPeer_R, timeout_, to_Re, liftId_Re, 
                             result, prevPeer, timeout, from_Co, to_Co, 
                             liftId_Co, nextPeer_C, liftValue_C, from_F, to, 
                             liftId_F, nextPeer, liftValue_F, cycle_, 
                             liftValue_, arbitrator_, toAct, lostMes, 
                             printBuffer >>

lpl(self) == /\ pc[self] = "lpl"
             /\ IF lostMes[self].type = "LiftProposeJSON" /\ lostMes[self].from = self
                   THEN /\ IF lostMes[self].liftId \in DOMAIN lifts[self] /\ lifts[self][lostMes[self].liftId].arbitrator /= self /\ lifts[self][lostMes[self].liftId].state = "Seek"
                              THEN /\ /\ arbitrator' = [arbitrator EXCEPT ![self] = lifts[self][lostMes[self].liftId].arbitrator]
                                      /\ from' = [from EXCEPT ![self] = self]
                                      /\ liftId' = [liftId EXCEPT ![self] = lostMes[self].liftId]
                                      /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "CheckTimeout",
                                                                               pc        |->  "lrlmf",
                                                                               from      |->  from[self],
                                                                               liftId    |->  liftId[self],
                                                                               arbitrator |->  arbitrator[self] ] >>
                                                                           \o stack[self]]
                                   /\ pc' = [pc EXCEPT ![self] = "CheckTimeout_"]
                              ELSE /\ pc' = [pc EXCEPT ![self] = "lrlmf"]
                                   /\ UNCHANGED << stack, from, liftId, 
                                                   arbitrator >>
                   ELSE /\ pc' = [pc EXCEPT ![self] = "lrlmf"]
                        /\ UNCHANGED << stack, from, liftId, arbitrator >>
             /\ UNCHANGED << Users, LiftProposers, ReliableUsers, Links, 
                             Cycles, tallies, messages, readMessages, 
                             lostMessages, lifts, startedNodes, nextLiftGuid, 
                             proposer, cycle, liftValue_P, arbitrator_P, 
                             nextPeer_, liftGuid, from_, to_, route_, 
                             liftValue_H, originator_, liftId_, arbitrator_H, 
                             prevPeer_, from_D, to_D, route_D, liftValue_D, 
                             originator_D, liftId_D, arbitrator_D, result_, 
                             from_C, to_C, route, liftValue, originator, 
                             liftId_C, arbitrator_C, result_C, to_R, liftId_R, 
                             result_R, prevPeer_R, timeout_, to_Re, liftId_Re, 
                             result, prevPeer, timeout, from_Co, to_Co, 
                             liftId_Co, nextPeer_C, liftValue_C, from_F, to, 
                             liftId_F, nextPeer, liftValue_F, cycle_, 
                             liftValue_, arbitrator_, toAct, lostMes, 
                             printBuffer >>

lrlmf(self) == /\ pc[self] = "lrlmf"
               /\ readMessages' = UNION{readMessages, {lostMes[self]}}
               /\ pc' = [pc EXCEPT ![self] = "l2w"]
               /\ UNCHANGED << Users, LiftProposers, ReliableUsers, Links, 
                               Cycles, tallies, messages, lostMessages, lifts, 
                               startedNodes, nextLiftGuid, stack, proposer, 
                               cycle, liftValue_P, arbitrator_P, nextPeer_, 
                               liftGuid, from_, to_, route_, liftValue_H, 
                               originator_, liftId_, arbitrator_H, prevPeer_, 
                               from_D, to_D, route_D, liftValue_D, 
                               originator_D, liftId_D, arbitrator_D, result_, 
                               from_C, to_C, route, liftValue, originator, 
                               liftId_C, arbitrator_C, result_C, to_R, 
                               liftId_R, result_R, prevPeer_R, timeout_, to_Re, 
                               liftId_Re, result, prevPeer, timeout, from_Co, 
                               to_Co, liftId_Co, nextPeer_C, liftValue_C, 
                               from_F, to, liftId_F, nextPeer, liftValue_F, 
                               from, liftId, arbitrator, cycle_, liftValue_, 
                               arbitrator_, toAct, lostMes, printBuffer >>

lpb(self) == /\ pc[self] = "lpb"
             /\ PrintT(printBuffer[self])
             /\ pc' = [pc EXCEPT ![self] = "Done"]
             /\ UNCHANGED << Users, LiftProposers, ReliableUsers, Links, 
                             Cycles, tallies, messages, readMessages, 
                             lostMessages, lifts, startedNodes, nextLiftGuid, 
                             stack, proposer, cycle, liftValue_P, arbitrator_P, 
                             nextPeer_, liftGuid, from_, to_, route_, 
                             liftValue_H, originator_, liftId_, arbitrator_H, 
                             prevPeer_, from_D, to_D, route_D, liftValue_D, 
                             originator_D, liftId_D, arbitrator_D, result_, 
                             from_C, to_C, route, liftValue, originator, 
                             liftId_C, arbitrator_C, result_C, to_R, liftId_R, 
                             result_R, prevPeer_R, timeout_, to_Re, liftId_Re, 
                             result, prevPeer, timeout, from_Co, to_Co, 
                             liftId_Co, nextPeer_C, liftValue_C, from_F, to, 
                             liftId_F, nextPeer, liftValue_F, from, liftId, 
                             arbitrator, cycle_, liftValue_, arbitrator_, 
                             toAct, lostMes, printBuffer >>

procId(self) == ProcStart(self) \/ l1(self) \/ lsn(self) \/ las(self)
                   \/ l2w(self) \/ l5(self) \/ l6(self) \/ l7(self)
                   \/ l8(self) \/ l9(self) \/ l10(self) \/ l4(self)
                   \/ clm(self) \/ lcl(self) \/ lpl(self) \/ lrlmf(self)
                   \/ lpb(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet:  \/ ProposeLift(self) \/ HandleLift(self)
                               \/ DecideLiftValidity(self)
                               \/ CheckLiftValidity(self)
                               \/ ReceiveLiftValidResult(self)
                               \/ ReceiveLiftCheckResult(self)
                               \/ CommitLift(self) \/ FailLift(self)
                               \/ CheckTimeout(self))
           \/ (\E self \in Users: procId(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Users : /\ WF_vars(procId(self))
                               /\ WF_vars(ProposeLift(self))
                               /\ WF_vars(HandleLift(self))
                               /\ WF_vars(CommitLift(self))
                               /\ WF_vars(FailLift(self))
                               /\ WF_vars(DecideLiftValidity(self))
                               /\ WF_vars(CheckLiftValidity(self))
                               /\ WF_vars(ReceiveLiftValidResult(self))
                               /\ WF_vars(ReceiveLiftCheckResult(self))
                               /\ WF_vars(CheckTimeout(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-2aabe8c935d5122506c5104fc303653e

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
    \* A.ConditionallyCommittedMoney < B.ConditionallyCommittedMoneykkkkkkkkkkkkkkkkk 
\* Game theory minimize everyone else

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
            /\ NoConversationBetween(x, y, messages, UNION{readMessages,lostMessages})
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
