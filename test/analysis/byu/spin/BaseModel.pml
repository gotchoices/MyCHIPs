#define N_PROCS 4
#define CANLIFT lift_in_progress
#define NUM_PAYMENTS 0 //number of payments allowed per node
#define NUM_LIFTS 1 //number of lifts the leader can call for
#define ALL_INITIALIZED initialized[0] && initialized[1] && initialized[2] && initialized[3]

byte foils[N_PROCS]
byte lowest_foil
byte stocks[N_PROCS]
chan upstream[N_PROCS] = [5] of { mtype, int }
chan downstream[N_PROCS] = [5] of { mtype, int }
mtype = { proposed_lift, verified_lift, poison, payment }
bool initialized[N_PROCS] = false


inline printState() {
    atomic{
        printf("\n")
        printf("\n")
        printf("******* ARROWS ARE DOWNSTREAM *******\n")
        printf("               -------               \n")
        printf("         ---%d |  0  | %d<--         \n", foils[0], stocks[0])
        printf("         |     -------     |         \n")
        printf("         |                 |         \n")
        printf("         v                 |         \n")
        printf("         %d                %d         \n", stocks[3], foils[1])
        printf("      -------           -------      \n")
        printf("      |  3  |           |  1  |      \n")
        printf("      -------           -------      \n")
        printf("         %d                %d         \n", foils[3], stocks[1])
        printf("         |                 ^         \n")
        printf("         |                 |         \n")
        printf("         |     -------     |         \n")
        printf("         -->%d |  2  | %d---         \n", stocks[2], foils[2])
        printf("               -------               \n")
        printf("\n")
        printf("\n")
    }
}

inline updateLowestFoil() {
    atomic{
        if
        :: (foils[0] <= foils[1] && foils[0] <= foils[2] && foils[0] <= foils[3]) -> lowest_foil = foils[0] 
        :: (foils[1] <= foils[0] && foils[1] <= foils[2] && foils[1] <= foils[3]) -> lowest_foil = foils[1] 
        :: (foils[2] <= foils[0] && foils[2] <= foils[1] && foils[2] <= foils[3]) -> lowest_foil = foils[2] 
        :: (foils[3] <= foils[0] && foils[3] <= foils[1] && foils[3] <= foils[2]) -> lowest_foil = foils[3] 
        :: else -> printf("ERROR, Couldn't conclude lowest foil value.")
        fi
    }
}

inline initializeNode(lift_val, payment_amt, next, prev, up_send, up_recv, down_recv, payments_remaining){
    lift_val = 0
    payment_amt = 0
    next = (id+1)%N_PROCS
    prev = (id+N_PROCS-1)%N_PROCS
    up_send = upstream[next]
    down_send = downstream[prev]
    up_recv = upstream[id]
    down_recv = downstream[id]
    payments_remaining = NUM_PAYMENTS
    initialized[id] = true
}

inline initializeLeader(lift_val, payment_amt, next, prev, up_send, down_send, up_recv, down_recv, lifts_remaining, lifts_completed, payments_remaining, lift_in_progress){
    lift_val = 0
    payment_amt = 0
    next = (id+1)%N_PROCS
    prev = (id+N_PROCS-1)%N_PROCS
    up_send = upstream[next]
    down_send = downstream[prev]
    up_recv = upstream[id]
    down_recv = downstream[id]
    lifts_remaining = NUM_LIFTS
    lifts_completed = 0
    payments_remaining = NUM_PAYMENTS
    lift_in_progress = false
    initialized[id] = true
}

inline nodeHandleProposedLift(down_recv, lift_val, down_send){

    down_recv?proposed_lift(lift_val)
    down_send!proposed_lift(lift_val)
}

inline nodeHandleVerifiedLift(up_recv, lift_val, up_send){

    up_recv?verified_lift(lift_val)
    stocks[id] = stocks[id] - lift_val
    up_send!verified_lift(lift_val)
    foils[id] = foils[id] - lift_val
}

inline nodeHandlePoison(down_recv, down_send){
    down_recv?poison(_)
    down_send!poison(0) 
    break
}

inline leaderSendProposedLift(down_send, lifts_remaining, lift_in_progress){
    updateLowestFoil()
    down_send!proposed_lift(lowest_foil)
    lifts_remaining = lifts_remaining - 1
    lift_in_progress = true
}

inline leaderHandleProposedLift(down_recv, lift_val, up_send){
    down_recv?proposed_lift(lift_val)
    stocks[id] = stocks[id] - lift_val
    up_send!verified_lift(lift_val)
    foils[id] = foils[id] - lift_val
}

inline leaderHandleVerifiedLift(up_recv, lift_val, lifts_completed, lift_in_progress){
    up_recv?verified_lift(lift_val)
    printf("success!  Lift_val: %d\n", lift_val)
    lifts_completed = lifts_completed + 1
    printState()
    if
    :: lifts_completed == NUM_LIFTS ->
        break
    :: else -> skip
    fi
    lift_in_progress = false
}

proctype node(byte id) {
    
    bool lift_in_progress
    int lift_val
    byte payment_amt
    byte next
    byte prev
    chan up_send
    chan down_send
    chan up_recv
    chan down_recv
    byte payments_remaining

        /*INITIALIZATION*/
    atomic
    {
        initializeNode(lift_val, payment_amt, next, prev, up_send, up_recv, down_recv, payments_remaining)
    }
    /*************************/
    ALL_INITIALIZED
    do
    :: down_recv?<proposed_lift(_)> ->
        atomic{
            nodeHandleProposedLift(down_recv, lift_val, down_send)
        }
        
    :: up_recv?<verified_lift(lift_val)> ->
        atomic{
            nodeHandleVerifiedLift(up_recv, lift_val, up_send)
        }

    :: down_recv?<poison(_)> ->
        atomic{
            nodeHandlePoison(down_recv, down_send)
        }
/*    :: down_recv?<payment(payment_amt)> ->
        atomic{
            down_recv?payment(payment_amt)
            stocks[id] = stocks[id] + payment_amt
        }
    :: payments_remaining > 0 ->
        atomic{
            down_send!payment(5)
            foils[id] = foils[id] + 5
            payments_remaining = payments_remaining - 1
        }*/ //Payments not used for this model
    od
    printState()

}

proctype leader(byte id) {
        /*INITIALIZATION*/
    int lift_val
    byte payment_amt
    byte next
    byte prev
    chan up_send
    chan down_send
    chan up_recv
    chan down_recv
    byte lifts_remaining
    byte lifts_completed
    byte payments_remaining
    bool lift_in_progress

    atomic{
        initializeLeader(lift_val, payment_amt, next, prev, up_send, down_send, up_recv, down_recv, lifts_remaining, lifts_completed, payments_remaining, lift_in_progress)
    }
    /*************************/
    ALL_INITIALIZED
    do
    :: lifts_remaining > 0 && !lift_in_progress ->
        atomic{
            leaderSendProposedLift(down_send, lifts_remaining, lift_in_progress)
        }
    :: down_recv?<proposed_lift(lift_val)> ->
        atomic{
            leaderHandleProposedLift(down_recv, lift_val, up_send)
        }
    :: up_recv?<verified_lift(lift_val)> ->
        atomic{
            leaderHandleVerifiedLift(up_recv, lift_val, lifts_completed, lift_in_progress)
        }

/*    :: down_recv?<payment(payment_amt)> ->
        atomic{
            down_recv?payment(payment_amt)
            stocks[id] = stocks[id] + payment_amt
        }
    :: payments_remaining > 0 ->
        atomic{
            down_send!payment(5)
            foils[id] = foils[id] + 5
            payments_remaining = payments_remaining - 1
        }*///Payments not used in this model
    od
    
    down_send!poison(0)
    printState()
}

init{
    atomic{
        run leader(0)
        run node(1)
        run node(2)
        run node(3)
        byte i
        byte balance_val
        for (i : 0 .. 3){
            if
            :: balance_val = 5
            :: balance_val = 10
            :: balance_val = 15
            :: balance_val = 20
            fi
            stocks[i] = balance_val
            foils[(i + 5) % 4] = balance_val
        }
        printState()
    }
}
// ->->->->->UPSTREAM->->->->->->
// <-<-<-<-<-DOWNSTREAM<-<-<-<-<-
// id 0 = A, 1 = B, 2 = C, 3 = D
// A stock == B foil, B stock == C foil, C stock == D foil, D stock == A foil


#define ABEqual (stocks[0] == foils[1])
#define BCEqual (stocks[1] == foils[2])
#define CDEqual (stocks[2] == foils[3])
#define DAEqual (stocks[3] == foils[0])
#define ABMessage (len(upstream[1]) != 0 || len(downstream[0]) != 0)
#define BCMessage (len(upstream[2]) != 0 || len(downstream[1]) != 0)
#define CDMessage (len(upstream[3]) != 0 || len(downstream[2]) != 0)
#define DAMessage (len(upstream[3]) != 0 || len(downstream[2]) != 0)


//There is always either equivalent stocks/foils or there is a message between the two participating nodes.  For all four balances.
ltl p1 {always (ABEqual || ABMessage) && (BCEqual || BCMessage) && (CDEqual || CDMessage) && (DAEqual || DAMessage)}


//There will always eventually be equivalent stocks/foils for each balance.
//Does not verify because of situation where a node receives the poison pill, then is sent a payment.
ltl p2 {always eventually ABEqual && BCEqual && CDEqual && DAEqual}


#define AOverLift (foils[0] < 0)
#define BOverLift (foils[1] < 0)
#define COverLift (foils[2] < 0)
#define DOverLift (foils[3] < 0)

//There will never be an overlift
ltl p3 {always (!AOverLift && !BOverLift && !COverLift && !DOverLift)}
