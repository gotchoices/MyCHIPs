#define N_NODES 2 //2 in lift 1 referee
#define LIFT_VALUE 5
chan succ[N_NODES] = [10] of { mtype }
chan pred[N_NODES] = [10] of { mtype }
chan ref[N_NODES] = [10] of { mtype }
chan to_referee = [10] of { mtype, chan }
mtype = {promise, status, pend, commit, void, signature}
byte state[N_NODES + 1] //plus ref
int balanceSuccDelta[N_NODES] = 0
int balancePredDelta[N_NODES] = 0

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
    if
    :: true ->
        printf("%d Sending %e to Pred\n", id, message)
        byte prev;
        prev = (id+N_NODES-1)%N_NODES; //find who it goes to
        succ[prev]!message; //put it in their succ box (if they are my pred I am their succ)
    :: true ->
        printf("%d Message to Pred Failed\n", id)
    fi
}

inline sendToSucc(message, id) {
    if
    :: true -> //Ssend the message
        printf("%d Sending %e to Succ\n", id, message)
        byte next;
        next = (id+1)%N_NODES; //find who it goes to
        pred[next]!message; //put it in their pred box (if they are my succ I am their pred)
    :: true -> //The message Failed to send
        printf("%d Message to Succ Failed\n", id)
    fi
}

inline sendToReferee(message, id) {
    printf("%d Sending %e to Ref\n", id, message)
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
  :: (ref[ORIGINATOR]?[pend]) -> //clear pend from chan in any state
    printf("Originator: Received Pend\n")
    statusUnresponded = false
    ref[ORIGINATOR]?pend
  :: (state[ORIGINATOR] == PEND && succ[ORIGINATOR]?[promise]) ->
    printf("Originator: Committing\n")
    succ[ORIGINATOR]?promise -> sendToReferee(commit, ORIGINATOR)
    state[ORIGINATOR] = CALL
  :: ((state[ORIGINATOR] == CALL || state[ORIGINATOR] == PEND) && ref[ORIGINATOR]?[void]) ->
      printf("Originator: Invalidating\n")
      statusUnresponded = false
      ref[ORIGINATOR]?void ->
      sendToSucc(void, ORIGINATOR)
      state[ORIGINATOR] = 2
      break
  :: (state[ORIGINATOR] == CALL && ref[ORIGINATOR]?[signature]);
      printf("Originator: Recieved Signature\n")
      statusUnresponded = false
      ref[ORIGINATOR]?signature ->
      sendToSucc(signature, ORIGINATOR)
      balanceSuccDelta[ORIGINATOR] = balanceSuccDelta[ORIGINATOR] + LIFT_VALUE
      balancePredDelta[ORIGINATOR] = balancePredDelta[ORIGINATOR] - LIFT_VALUE
      state[ORIGINATOR] = 1
  :: (state[ORIGINATOR] == 1 && pred[ORIGINATOR]?[signature]);
      printf("Originator: Recieved Signature, Lift Complete\n")
      pred[ORIGINATOR]?signature ->
      state[ORIGINATOR] = 1
      break
  od

}

proctype referee() {
  chan returnChan
  state[REFEREE] = NO_LIFT
  do
  :: (state[REFEREE] == NO_LIFT && to_referee?[status(returnChan)]) ->
      printf("Referee: Replying Pend\n")
      to_referee?status(returnChan) ->
      returnChan!pend
  :: (state[REFEREE] == NO_LIFT && to_referee?[status(returnChan)]) ->
      printf("Referee: Ruling and Replying Void\n")
      to_referee?status(returnChan) ->
      returnChan!void
      state[REFEREE] = 2
  :: (state[REFEREE] == NO_LIFT && to_referee?[commit(returnChan)]) ->
      printf("Referee: Ruling and Replying to Commit Void\n")
      to_referee?commit(returnChan) ->
      returnChan!void
      state[REFEREE] = 2
  :: (state[REFEREE] == NO_LIFT && to_referee?[commit(returnChan)]) ->
      printf("Referee: Ruling and Replying to Commit Signature\n")
      to_referee?commit(returnChan) ->
      returnChan!signature
      state[REFEREE] = 1
  :: (state[REFEREE] == 1 && to_referee?[status(returnChan)]) ->
      printf("Referee: Replying from cache Signature\n")
      to_referee?status(returnChan) ->
      returnChan!signature
  :: (state[REFEREE] == 2 && to_referee?[status(returnChan)]) ->
      printf("Referee: Replying from cache Void\n")
      to_referee?status(returnChan) ->
      returnChan!void
  :: (state[REFEREE] == 2 && to_referee?[commit(returnChan)]) ->
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
    succ[RELAY]?promise -> sendToPred(promise, RELAY)
    state[RELAY] = PEND
  :: (state[RELAY] == PEND && !statusUnresponded) ->
    printf("Relay: Requesting Status\n")
    true -> sendToReferee(status, RELAY)
    statusUnresponded = true
    state[RELAY] = PEND
  :: (ref[RELAY]?[pend]) -> //clear pend from chan in any state
    printf("Relay: Received Pend\n")
    statusUnresponded = false
    ref[RELAY]?pend
  :: (state[RELAY] == PEND && ref[RELAY]?[void]) ->
    statusUnresponded = false
    ref[RELAY]?void ->
      printf("Relay: Invalidating\n")
      sendToSucc(void, RELAY)
      state[RELAY] = 2
      break
  :: (state[RELAY] == PEND && pred[RELAY]?[void]) ->
    pred[RELAY]?void ->
      printf("Relay: Invalidating\n")
      sendToSucc(void, RELAY)
      state[RELAY] = 2
      break
  :: (state[RELAY] == PEND && ref[RELAY]?[signature]);
      printf("Relay: Received Signature from Ref\n")
      ref[RELAY]?signature ->
      balancePredDelta[RELAY] = balancePredDelta[RELAY] - LIFT_VALUE
      sendToSucc(signature, RELAY)
      balanceSuccDelta[RELAY] = balanceSuccDelta[RELAY] + LIFT_VALUE
      state[RELAY] = 1
      break
  :: (state[RELAY] == PEND && pred[RELAY]?[signature]);
      printf("Relay: Received Signature\n")
      pred[RELAY]?signature ->
      balancePredDelta[RELAY] = balancePredDelta[RELAY] - LIFT_VALUE
      sendToSucc(signature, RELAY)
      balanceSuccDelta[RELAY] = balanceSuccDelta[RELAY] + LIFT_VALUE
      state[RELAY] = 1
      break
  od

}

init {
  atomic {
    run originator()
    run relay()
    run referee()
  }
}

#define fair ((state[REFEREE] == GOOD || state[REFEREE] == VOID))

ltl fairPathExists {(always (! fair))} // should fail

ltl p1 {always eventually (fair implies (state[ORIGINATOR] != PEND && state[RELAY] != PEND && state[REFEREE] != NO_LIFT))}

ltl p2 {always eventually (fair implies ((state[REFEREE] == GOOD implies state[ORIGINATOR] == GOOD) && (state[ORIGINATOR] == GOOD implies state[RELAY] == GOOD) && (state[RELAY] == GOOD implies state[REFEREE] == GOOD)))}

ltl p3 {always eventually (fair implies ((balanceSuccDelta[ORIGINATOR] + balancePredDelta[ORIGINATOR] >= 0)
                                       && (balanceSuccDelta[RELAY] + balancePredDelta[RELAY] >= 0)
                                       ))}

ltl p4 {always eventually (fair implies ((balanceSuccDelta[ORIGINATOR] == -balancePredDelta[RELAY])
                                      && (balanceSuccDelta[RELAY] == -balancePredDelta[ORIGINATOR])
                                      ))}

ltl test1 {always eventually ( !( (balanceSuccDelta[ORIGINATOR] + balancePredDelta[ORIGINATOR] > 0)
                               || (balanceSuccDelta[RELAY] + balancePredDelta[RELAY] > 0)))}
