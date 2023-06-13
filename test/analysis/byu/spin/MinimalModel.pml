#define N_NODES 2 //2 in lift 1 referee
#define LIFT_VALUE 5
chan succ[N_NODES] = [10] of { mtype }
chan pred[N_NODES] = [10] of { mtype }
chan ref[N_NODES] = [10] of { mtype }
chan to_referee = [10] of { mtype, chan }
mtype = {promise, status, commit, void, signature}
byte state[N_NODES + 1] //plus ref
int balanceSuccDelta[N_NODES] = 0
int balancePredDelta[N_NODES] = 0
typedef ActionStatus {
  bool promise_send;
  bool promise_receive;
  bool commit_send;
  bool commit_receive;
  bool ref_send;
  bool ref_receive;
}
//This is a variable used only to compare with coq properties
//It is hidden from the state because it is a write only variable
hidden ActionStatus act_status[N_NODES] = 0

#define ORIGINATOR 0
#define RELAY 1
#define REFEREE 2
#define NO_LIFT 0
#define GOOD 1
#define VOID 2
#define PEND 3
#define CALL 4

inline sendToPred(message, id) {
    //TODO: make some messages fail
    atomic {
    if
    :: true ->
        printf("%d Sending %e to Pred\n", id, message)
        byte prev;
        prev = (id+N_NODES-1)%N_NODES; //find who it goes to
        if 
        :: message == promise -> act_status[id].promise_send = true;
        :: message == void -> act_status[id].commit_send = true;
        :: message == signature -> act_status[id].commit_send = true;
        :: else -> true
        fi
        succ[prev]!message; //put it in their succ box (if they are my pred I am their succ)
    :: true ->
        printf("%d Message to Pred Failed\n", id)
    fi
    }
}

inline sendToSucc(message, id) {
    atomic {
    if
    :: true -> //Ssend the message
        printf("%d Sending %e to Succ\n", id, message)
        byte next;
        next = (id+1)%N_NODES; //find who it goes to
        if 
        :: message == promise -> act_status[id].promise_send = true;
        :: message == void -> act_status[id].commit_send = true;
        :: message == signature -> act_status[id].commit_send = true;
        :: else -> true
        fi
        pred[next]!message; //put it in their pred box (if they are my succ I am their pred)
    :: true -> //The message Failed to send
        printf("%d Message to Succ Failed\n", id)
    fi
    }
}

inline sendToReferee(message, id) {
    printf("%d Sending %e to Ref\n", id, message)
    act_status[id].ref_send = true
    to_referee!message(ref[id]); //put it in the referee's in box with a return channel for the response
}

proctype originator() {
  bool statusUnresponded //flag to only send referee one status request (the ref will always eventually respond so this is sufficient)
  state[ORIGINATOR] = NO_LIFT
  statusUnresponded = false
  do
  :: (state[ORIGINATOR] == NO_LIFT) ->
    printf("Originator: Initiating Lift\n")
    true -> sendToPred(promise, ORIGINATOR)
    state[ORIGINATOR] = PEND
  :: (state[ORIGINATOR] == PEND && !statusUnresponded) ->
    printf("Originator: Requesting Status\n")
    statusUnresponded = true
    true -> sendToReferee(status, ORIGINATOR)
    state[ORIGINATOR] = PEND
  :: (state[ORIGINATOR] == PEND && succ[ORIGINATOR]?[promise]) ->
    printf("Originator: Committing\n")
    succ[ORIGINATOR]?promise -> sendToReferee(commit, ORIGINATOR)
    assert(!act_status[ORIGINATOR].promise_receive == true)
    act_status[ORIGINATOR].promise_receive = true
    state[ORIGINATOR] = CALL
  :: ((state[ORIGINATOR] == PEND) && ref[ORIGINATOR]?[void]) ->
      printf("Originator: Invalidating\n")
      statusUnresponded = false
      ref[ORIGINATOR]?void
      assert(!act_status[ORIGINATOR].ref_receive == true)
      act_status[ORIGINATOR].ref_receive = true
      //DONT FORWARD STATUS REQUEST
      //sendToSucc(void, ORIGINATOR)
      state[ORIGINATOR] = VOID
      break
  :: ((state[ORIGINATOR] == CALL) && ref[ORIGINATOR]?[void]) ->
      printf("Originator: Invalidating\n")
      statusUnresponded = false
      ref[ORIGINATOR]?void ->
      sendToSucc(void, ORIGINATOR)
      state[ORIGINATOR] = VOID
      break
  :: (state[ORIGINATOR] == CALL && ref[ORIGINATOR]?[signature]);
      printf("Originator: Recieved Signature\n")
      statusUnresponded = false
      ref[ORIGINATOR]?signature ->
      sendToSucc(signature, ORIGINATOR)
      balanceSuccDelta[ORIGINATOR] = balanceSuccDelta[ORIGINATOR] + LIFT_VALUE
      balancePredDelta[ORIGINATOR] = balancePredDelta[ORIGINATOR] - LIFT_VALUE
      state[ORIGINATOR] = GOOD
  :: (state[ORIGINATOR] == GOOD && pred[ORIGINATOR]?[signature]);
      printf("Originator: Recieved Signature, Lift Complete\n")
      assert(!act_status[ORIGINATOR].commit_receive == true)
      act_status[ORIGINATOR].commit_receive = true
      pred[ORIGINATOR]?signature ->
      state[ORIGINATOR] = GOOD
      break
  od
}

proctype referee() {
  chan returnChan
  state[REFEREE] = NO_LIFT
  do
  :: (state[REFEREE] == NO_LIFT && to_referee?[status(returnChan)]) ->
      printf("Referee: Ruling and Replying Void\n")
      to_referee?status(returnChan) ->
      returnChan!void
      state[REFEREE] = VOID
  :: (state[REFEREE] == NO_LIFT && to_referee?[commit(returnChan)]) ->
      printf("Referee: Ruling and Replying to Commit Void\n")
      to_referee?commit(returnChan) ->
      returnChan!void
      state[REFEREE] = VOID
  :: (state[REFEREE] == NO_LIFT && to_referee?[commit(returnChan)]) ->
      printf("Referee: Ruling and Replying to Commit Signature\n")
      to_referee?commit(returnChan) ->
      returnChan!signature
      state[REFEREE] = GOOD
  :: (state[REFEREE] == GOOD && to_referee?[status(returnChan)]) ->
      printf("Referee: Replying from cache Signature\n")
      to_referee?status(returnChan) ->
      returnChan!signature
  :: (state[REFEREE] == VOID && to_referee?[status(returnChan)]) ->
      printf("Referee: Replying from cache Void\n")
      to_referee?status(returnChan) ->
      returnChan!void
  :: (state[REFEREE] == VOID && to_referee?[commit(returnChan)]) ->
      printf("Referee: Replying to Commit from cache Void\n")
      to_referee?commit(returnChan) ->
      returnChan!void
  :: (timeout) -> break
  od
}

proctype relay() {

  bool statusUnresponded
  state[RELAY] = NO_LIFT
  statusUnresponded = false
  do
  :: (state[RELAY] == NO_LIFT && succ[RELAY]?[promise]) ->
    printf("Relay: Received Promise\n")
    assert(!act_status[RELAY].promise_receive == true)
    act_status[RELAY].promise_receive = true
    succ[RELAY]?promise -> sendToPred(promise, RELAY)
    state[RELAY] = PEND
  :: (state[RELAY] == PEND && !statusUnresponded) ->
    printf("Relay: Requesting Status\n")
    true -> sendToReferee(status, RELAY)
    statusUnresponded = true
    state[RELAY] = PEND
  :: (state[RELAY] == PEND && ref[RELAY]?[void]) ->
    statusUnresponded = false
    ref[RELAY]?void ->
      printf("Relay: Invalidating\n")
      //Don't forward if got from ref
      //sendToSucc(void, RELAY)
      assert(!act_status[RELAY].ref_receive == true)
      act_status[RELAY].ref_receive = true
      state[RELAY] = VOID
      break
  :: (state[RELAY] == PEND && pred[RELAY]?[void]) ->
    pred[RELAY]?void ->
      printf("Relay: Invalidating\n")
      assert(!act_status[RELAY].commit_receive == true)
      act_status[RELAY].commit_receive = true
      /*Oportunity to break atomic action to receive a ref result*/
      if 
        :: ref[RELAY]?[signature] 
          ref[RELAY]?signature ->
            assert(false)
        :: ref[RELAY]?[void] 
          ref[RELAY]?void ->
            assert(!act_status[RELAY].ref_receive == true)
            act_status[RELAY].ref_receive = true
        :: else -> true
      fi
      sendToSucc(void, RELAY)
      state[RELAY] = VOID
      break
  :: (state[RELAY] == PEND && ref[RELAY]?[signature]);
      printf("Relay 1: Received Signature from Ref\n")
      ref[RELAY]?signature ->
      balancePredDelta[RELAY] = balancePredDelta[RELAY] - LIFT_VALUE
      //sendToSucc(signature, RELAY)
      //Don't forward if got from ref
      balanceSuccDelta[RELAY] = balanceSuccDelta[RELAY] + LIFT_VALUE
      assert(!act_status[RELAY].ref_receive == true)
      act_status[RELAY].ref_receive = true
      state[RELAY] = GOOD
      break
  :: (state[RELAY] == PEND && pred[RELAY]?[signature]);
      printf("Relay 1: Received Signature\n")
      assert(!act_status[RELAY].commit_receive == true)
      act_status[RELAY].commit_receive = true
      pred[RELAY]?signature ->
      /*Oportunity to break atomic action to receive a ref result*/
      if 
        :: ref[RELAY]?[signature] 
          ref[RELAY]?signature ->
            assert(!act_status[RELAY].ref_receive == true)
            act_status[RELAY].ref_receive = true
        :: ref[RELAY]?[void] 
          ref[RELAY]?void ->
            assert(false)
        :: else -> true
      fi
      balancePredDelta[RELAY] = balancePredDelta[RELAY] - LIFT_VALUE
      sendToSucc(signature, RELAY)
      balanceSuccDelta[RELAY] = balanceSuccDelta[RELAY] + LIFT_VALUE
      state[RELAY] = GOOD
      break
  od
  do
    :: (pred[RELAY]?[signature]);
      assert(!act_status[RELAY].commit_receive == true)
      act_status[RELAY].commit_receive = true
      pred[RELAY]?signature ->
      sendToSucc(signature, RELAY)
    :: (pred[RELAY]?[void]);
      assert(!act_status[RELAY].commit_receive == true)
      act_status[RELAY].commit_receive = true
      pred[RELAY]?void ->
      sendToSucc(void, RELAY)
    :: (ref[RELAY]?[void]);
      assert(!act_status[RELAY].ref_receive == true)
      act_status[RELAY].ref_receive = true
      pred[RELAY]?void -> true
    :: (ref[RELAY]?[signature]);
      assert(!act_status[RELAY].ref_receive == true)
      act_status[RELAY].ref_receive = true
      pred[RELAY]?signature -> true
    :: timeout -> break
  od

}

init {
  atomic {
    int i;
    for (i : 1 .. N_NODES) {
      act_status[i-1].promise_send = false;
      act_status[i-1].promise_receive = false;
      act_status[i-1].commit_send = false;
      act_status[i-1].commit_receive = false;
      act_status[i-1].ref_send = false;
      act_status[i-1].ref_receive = false;
    }
    run originator()
    run relay()
    run referee()
  }
}

ltl p1 {always eventually (state[ORIGINATOR] != PEND && state[RELAY] != PEND && state[REFEREE] != NO_LIFT)}

ltl p2 {always eventually ((state[REFEREE] == GOOD implies state[ORIGINATOR] == GOOD) && (state[ORIGINATOR] == GOOD implies state[RELAY] == GOOD) && (state[RELAY] == GOOD implies state[REFEREE] == GOOD))}

ltl p3 {always eventually ((balanceSuccDelta[ORIGINATOR] + balancePredDelta[ORIGINATOR] >= 0)
                                       && (balanceSuccDelta[RELAY] + balancePredDelta[RELAY] >= 0)
                                       )}

ltl p4 {always eventually ((balanceSuccDelta[ORIGINATOR] == -balancePredDelta[RELAY])
                                      && (balanceSuccDelta[RELAY] == -balancePredDelta[ORIGINATOR])
                                      )}

#define size_fair (state[ORIGINATOR] != NO_LIFT && state[RELAY] != NO_LIFT && state[REFEREE] != NO_LIFT)

ltl size_fair_path_exists {
  always (!size_fair)
}

ltl hra {always eventually (size_fair implies (
  (act_status[ORIGINATOR].promise_send) && 
  (act_status[RELAY].promise_receive) && 
  (act_status[RELAY].commit_receive || (act_status[RELAY].ref_send && act_status[RELAY].ref_receive))
))}
//has no duplicate receives confirmed with asserts
//all receives causal confirmed by promela semantics by inspection
ltl ast {always (
  (act_status[RELAY].promise_send -> act_status[RELAY].promise_receive) &&
  (act_status[RELAY].commit_send -> act_status[RELAY].commit_receive)
)}
//all ids in range true by inspection
//promise forward commit backward true by inspection
ltl psc0 {always (
  (act_status[RELAY].commit_send -> act_status[ORIGINATOR].commit_send) &&
  (act_status[ORIGINATOR].commit_receive -> act_status[ORIGINATOR].commit_send) &&
  (act_status[RELAY].commit_receive -> act_status[ORIGINATOR].commit_send) &&
  (act_status[ORIGINATOR].promise_receive -> act_status[RELAY].promise_send) &&
  (act_status[ORIGINATOR].commit_receive -> act_status[RELAY].commit_send) 
)}
never psc1 {
  do
    :: (!act_status[RELAY].promise_send && act_status[RELAY].ref_send) -> break
    :: else -> true
  od
  do
    :: (act_status[RELAY].promise_send && act_status[RELAY].ref_send) -> break
    :: else -> true
  od
}
never psc2 {
  do
    :: (!act_status[ORIGINATOR].promise_send && act_status[ORIGINATOR].ref_send) -> break
    :: else -> true
  od
  do
    :: (act_status[ORIGINATOR].promise_send && act_status[ORIGINATOR].ref_send) -> break
    :: else -> true
  od
}
never psc3 {
  do
    :: (act_status[RELAY].commit_send && !act_status[RELAY].ref_send) -> break
    :: else -> true
  od
  do
    :: (act_status[RELAY].commit_send && act_status[RELAY].ref_send) -> break
    :: else -> true
  od
}
never psc4 {
  do
    :: (!act_status[ORIGINATOR].promise_send && act_status[ORIGINATOR].ref_send) -> break
    :: else -> true
  od
  do
    :: (act_status[ORIGINATOR].promise_send && act_status[ORIGINATOR].ref_send) -> break
    :: else -> true
  od
}

ltl rrc {always (
  (act_status[ORIGINATOR].ref_receive -> act_status[ORIGINATOR].ref_send) &&
  (act_status[RELAY].ref_receive -> act_status[RELAY].ref_send)
)}

never eqc0 { //[RP, SS, RS]
  do
    :: (act_status[RELAY].promise_receive && !act_status[RELAY].ref_send) -> break
    :: else -> true
  od
  do
    :: (act_status[RELAY].ref_send && !act_status[RELAY].ref_receive) -> break
    :: else -> true
  od
  do
    :: (act_status[RELAY].ref_receive) -> break
    :: else -> true
  od
  //CHECK MISSING ITEMS AT END
  do
    :: !act_status[RELAY].promise_send -> break
    :: else -> true
  od
}
never eqc1 { //[RP, SP, SS, RS]
  do
    :: (act_status[RELAY].promise_receive && !act_status[RELAY].promise_send) -> break
    :: else -> true
  od
  do
    :: (act_status[RELAY].promise_send && !act_status[RELAY].ref_send) -> break
    :: else -> true
  od
  do
    :: (act_status[RELAY].ref_send && !act_status[RELAY].ref_receive) -> break
    :: else -> true
  od
  do
    :: (act_status[RELAY].ref_receive) -> break
    :: else -> true
  od
}
never eqc2 { //[RP, SS, SP, RS] //SANITY CHECK THIS SHOULDN'T HAPPEN
  do
    :: (act_status[RELAY].promise_receive && !act_status[RELAY].ref_send) -> break
    :: else -> true
  od
  do
    :: (act_status[RELAY].ref_send && !act_status[RELAY].promise_send) -> break
    :: else -> true
  od
  do
    :: (act_status[RELAY].promise_send && !act_status[RELAY].ref_receive) -> break
    :: else -> true
  od
  do
    :: (act_status[RELAY].ref_receive) -> break
    :: else -> true
  od
}
never eqc3 { //[RP, SP, RC, SS, RS] //SANITY CHECK THIS SHOULDN'T HAPPEN
  do
    :: (act_status[RELAY].promise_receive && !act_status[RELAY].promise_send) -> break
    :: else -> true
  od
  do
    :: (act_status[RELAY].promise_send && !act_status[RELAY].commit_receive) -> break
    :: else -> true
  od
  do
    :: (act_status[RELAY].commit_receive && !act_status[RELAY].ref_send) -> break
    :: else -> true
  od
  do
    :: (act_status[RELAY].ref_send && !act_status[RELAY].ref_receive) -> break
    :: else -> true
  od
  do
    :: (act_status[RELAY].ref_receive) -> break
    :: else -> true
  od
}
never eqc4 { //[RP, SP, RC]
  do
    :: (act_status[RELAY].promise_receive && !act_status[RELAY].promise_send) -> break
    :: else -> true
  od
  do
    :: (act_status[RELAY].promise_send && !act_status[RELAY].commit_receive) -> break
    :: else -> true
  od
  do
    :: (act_status[RELAY].commit_receive) -> break
    :: else -> true
  od
  //CHECK MISSING ITEMS AT END
  do
    :: !act_status[RELAY].commit_send && !act_status[RELAY].ref_send -> break
    :: else -> true
  od
}
never eqc5 { // [RP, SP, RC, SC]
  do
    :: (act_status[RELAY].promise_receive && !act_status[RELAY].promise_send) -> break
    :: else -> true
  od
  do
    :: (act_status[RELAY].promise_send && !act_status[RELAY].commit_receive) -> break
    :: else -> true
  od
  do
    :: (act_status[RELAY].commit_receive && !act_status[RELAY].commit_send) -> break
    :: else -> true
  od
  do
    :: (act_status[RELAY].commit_send) -> break
    :: else -> true
  od
  //CHECK MISSING ITEMS AT END
  do
    :: !act_status[RELAY].ref_send -> break
    :: else -> true
  od
}
never eqc6 { // [RP, SP, SS, RC, RS]
  do
    :: (act_status[RELAY].promise_receive && !act_status[RELAY].promise_send) -> break
    :: else -> true
  od
  do
    :: (act_status[RELAY].promise_send && !act_status[RELAY].commit_receive) -> break
    :: else -> true
  od
  do
    :: (act_status[RELAY].ref_send && !act_status[RELAY].commit_receive) -> break
    :: else -> true
  od
  do
    :: (act_status[RELAY].commit_receive && !act_status[RELAY].ref_receive) -> break
    :: else -> true
  od
  do
    :: (act_status[RELAY].ref_receive || ref[RELAY]?[void] || ref[RELAY]?[signature]) -> break
    //If its in our queue we may not process it but it still is received
    :: else -> true
  od
  //CHECK MISSING ITEMS AT END
  do
    :: !act_status[RELAY].commit_send -> break
    :: else -> true
  od
}
never eqc7 { // [RP, SP, SS, RS, RC]
  do
    :: (act_status[RELAY].promise_receive && !act_status[RELAY].promise_send) -> break
    :: else -> true
  od
  do
    :: (act_status[RELAY].promise_send && !act_status[RELAY].ref_send) -> break
    :: else -> true
  od
  do
    :: (act_status[RELAY].ref_send && !act_status[RELAY].ref_receive) -> break
    :: else -> true
  od
  do
    :: (act_status[RELAY].ref_receive && !act_status[RELAY].commit_receive) -> break
    :: else -> true
  od
  do
    :: (act_status[RELAY].commit_receive) -> break
      //If its in our queue we may not process it but it still is received
    :: else -> true
  od
}
never eqc8 { // [RP, SP, SS, RS, RC, SC]
  do
    :: (act_status[RELAY].promise_receive && !act_status[RELAY].promise_send) -> break
    :: else -> true
  od
  do
    :: (act_status[RELAY].promise_send && !act_status[RELAY].ref_send) -> break
    :: else -> true
  od
  do
    :: (act_status[RELAY].ref_send && !act_status[RELAY].ref_receive) -> break
    :: else -> true
  od
  do
    :: (act_status[RELAY].ref_receive && !act_status[RELAY].commit_receive) -> break
    :: else -> true
  od
  do
    :: (act_status[RELAY].commit_receive && !act_status[RELAY].commit_send) -> break
    :: else -> true
  od
  do
    :: (act_status[RELAY].commit_send) -> break
    :: else -> true
  od
}
never eqc9 { // [RP, SP, SS, RC, RS, SC]
  do
    :: (act_status[RELAY].promise_receive && !act_status[RELAY].promise_send) -> break
    :: else -> true
  od
  do
    :: (act_status[RELAY].promise_send && !act_status[RELAY].ref_send) -> break
    :: else -> true
  od
  do
    :: (act_status[RELAY].ref_send && !act_status[RELAY].ref_receive) -> break
    :: else -> true
  od
  do
    :: (act_status[RELAY].commit_receive && !act_status[RELAY].ref_receive) -> break
    :: else -> true
  od
  do
    :: (act_status[RELAY].ref_receive && !act_status[RELAY].commit_send) -> break
    :: else -> true
  od
  do
    :: (act_status[RELAY].commit_send) -> break
    :: else -> true
  od
}
never eqc10 { // [RP, SP, SS, RC, SC, RS]
  do
    :: (act_status[RELAY].promise_receive && !act_status[RELAY].promise_send) -> break
    :: else -> true
  od
  do
    :: (act_status[RELAY].promise_send && !act_status[RELAY].ref_send) -> break
    :: else -> true
  od
  do
    :: (act_status[RELAY].ref_send && !act_status[RELAY].ref_receive) -> break
    :: else -> true
  od
  do
    :: (act_status[RELAY].commit_receive && !act_status[RELAY].commit_send) -> break
    :: else -> true
  od
  do
    :: (act_status[RELAY].commit_send && !act_status[RELAY].ref_receive) -> break
    :: else -> true
  od
  do
    :: (act_status[RELAY].ref_receive) -> break
    :: else -> true
  od
}

/*
[PR, SS, SR]
[PR, PS, SS, SR]
[PR, SS, PS, SR] //SANITY CHECK THIS SHOULDN'T HAPPEN
[PR, PS, CR, SS, SR] //SANITY CHECK THIS SHOULDN'T HAPPEN
[PR, PS, CR]
[PR, PS, CR, CS]
[PR, PS, SS, CR, SR]
[PR, PS, SS, SR, CR]
[PR, PS, SS, SR, CR, CS]
[PR, PS, SS, CR, SR, CS]
[PR, PS, SS, CR, CS, SR]
*/

