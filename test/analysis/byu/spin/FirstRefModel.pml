#define N_PROCS 4
#define NUM_PAYMENTS 0
#define NUM_LIFTS 1 //number of lifts the leader can call for
#define ALL_INITIALIZED initialized[0] && initialized[1] && initialized[2] && initialized[3] && initialized[4]
#define MAX_INVALID_LIFTS 50


typedef Lift {
    byte value;
    byte id;
}


byte foils[N_PROCS]
byte lowest_foil
byte stocks[N_PROCS]
byte conditional[N_PROCS]
chan upstream[N_PROCS] = [5] of {mtype, Lift}
chan downstream[N_PROCS] = [5] of {mtype, Lift}
chan toRef[N_PROCS] = [5] of {mtype, Lift}
chan fromRef[N_PROCS] = [5] of {mtype, Lift}
int next_lift_id = 1

mtype = { proposed_lift, verified_lift, poison, payment }
mtype = { checkLiftValidity, liftValid, liftInvalid }
bool initialized[N_PROCS + 1] = false

//NODE MACROS
#define initializeNode(id, payment_amt, next, prev, up_send, down_send, up_recv, down_recv, payments_remaining, lift_in_progress, to_ref, from_ref, num_lifts_invalid, cur_lift_invalid) {\
    payment_amt = 0;\
    next = (id+1)%N_PROCS;\
    prev = (id+N_PROCS-1)%N_PROCS;\
    up_send = upstream[next];\
    down_send = downstream[prev];\
    up_recv = upstream[id];\
    down_recv = downstream[id];\
    payments_remaining = NUM_PAYMENTS;\
    initialized[id] = true;\
    lift_in_progress = false;\
    to_ref = toRef[id];\
    from_ref = fromRef[id];\
    num_lifts_invalid = 0;\
    cur_lift_invalid = false}

#define nodeHandleProposedLift(id, down_recv, down_send, cur_lift, lift_in_progress) {\
    down_recv?proposed_lift(cur_lift);\
    down_send!proposed_lift(cur_lift);\
    conditional[id] = conditional[id] + cur_lift.value;\
    lift_in_progress = true;}

#define nodeHandleVerifiedLift(id, cur_lift_invalid, num_lifts_invalid, invalid_lifts, cur_lift, up_recv, up_send, lift_in_progress) {\
    cur_lift_invalid = false;\
    printf("num_lifts_invalid: %d\n", num_lifts_invalid);\
    for(i : 0 .. num_lifts_invalid){\
        if\
        :: invalid_lifts[i] == cur_lift.id ->\
            cur_lift_invalid = true;\
            break;\
        :: else -> skip;\
        fi\
    }\
    if\
    :: cur_lift_invalid ->\
        up_recv?verified_lift(cur_lift);\
    :: else ->\
        up_recv?verified_lift(cur_lift);\
        stocks[id] = stocks[id] - cur_lift.value;\
        up_send!verified_lift(cur_lift);\
        foils[id] = foils[id] - cur_lift.value;\
        conditional[id] = conditional[id] - cur_lift.value;\
        lift_in_progress = false;\
        printf("node %d verified lift %d\n", id, cur_lift.id);\
    fi}

#define nodeHandlePoison(down_recv, down_send) {\
    Lift dummy;\
    down_recv?poison(dummy);\
    down_send!poison(dummy);\
    break;}
//MALNODE MACROS
#define malNodeHandleVerifiedLift(id, up_recv, cur_lift, up_send) {\
    up_recv?verified_lift(cur_lift);\
    stocks[id] = stocks[id] - cur_lift.value;\
    if\
    :: true ->\
        up_send!verified_lift(cur_lift);\
        foils[id] = foils[id] - cur_lift.value;\
    :: true ->\
        skip;\
    fi}
//LEADER MACROS
#define initializeLeader(id, payment_amt, next, prev, up_send, down_send, up_recv, down_recv, lifts_remaining, lifts_completed, payments_remaining, lift_in_progress, to_ref, from_ref) {\
    payment_amt = 0;\
    next = (id+1)%N_PROCS;\
    prev = (id+N_PROCS-1)%N_PROCS;\
    up_send = upstream[next];\
    down_send = downstream[prev];\
    up_recv = upstream[id];\
    down_recv = downstream[id];\
    lifts_remaining = NUM_LIFTS;\
    lifts_completed = 0;\
    payments_remaining = NUM_PAYMENTS;\
    lift_in_progress = false;\
    initialized[id] = true;\
    to_ref = toRef[0];\
    from_ref = fromRef[0];}

#define leaderSendProposedLift(down_send, lifts_remaining, lift_in_progress) {\
    updateLowestFoil();\
    Lift new_lift;\
    new_lift.value = lowest_foil;\
    new_lift.id = next_lift_id;\
    down_send!proposed_lift(new_lift);\
    next_lift_id = next_lift_id + 1;\
    lifts_remaining = lifts_remaining - 1;\
    conditional[0] = conditional[0] + new_lift.value;\
    lift_in_progress = true;}
//TODO:: Change conditional[0] to conditional[id], pass in id to macro

#define leaderHandleProposedLift(down_recv, cur_lift, to_ref, from_ref, up_send, lift_in_progress, lifts_remaining, num_lifts_invalid, invalid_lifts, cur_lift_invalid) {\
    down_recv?proposed_lift(cur_lift);\
    cur_lift_invalid = false;\
    for(i : 0 .. num_lifts_invalid){\
        if\
        :: invalid_lifts[i] == cur_lift.id ->\
            cur_lift_invalid = true;\
            break;\
        :: else -> skip;\
        fi\
    }\
    if\
    :: cur_lift_invalid -> skip;\
    :: else ->\
        printf("Leader Requesting Ref Check...\n");\
        to_ref!checkLiftValidity(cur_lift);\
        if\
        :: from_ref?<liftInvalid(cur_lift)> ->\
            from_ref?liftInvalid(cur_lift);\
            conditional[0] = conditional[0] - cur_lift.value;\
            lift_in_progress = false;\
            lifts_remaining = lifts_remaining + 1;\
            printf("lift aborted!\nLift_id: %d\nLift_val: %d\n", cur_lift.id, cur_lift.value);\
        :: from_ref?<liftValid(cur_lift)> ->\
            from_ref?liftValid(cur_lift);\
            stocks[id] = stocks[id] - cur_lift.value;\
            up_send!verified_lift(cur_lift);\
            foils[id] = foils[id] - cur_lift.value;\
        fi\
    fi}

//TODO:: Change conditional[0] to conditional[id], pass in id to macro

//REF MACROS
#define refCheckLiftValidForNode(node_id) {\
    toRef[node_id]?licheckLiftValidity(cur_ft);\
    cur_lift_invalid = false;\
    for(i : 0 .. num_lifts_invalid){\
        if\
        :: invalid_lifts[i] == cur_lift.id ->\
            fromRef[node_id]!liftInvalid(cur_lift);\
            cur_lift_invalid = true;\
            break;\
        :: else -> skip;\
        fi\
    }\
    if\
    :: cur_lift_invalid -> cur_lift_invalid = false;\
    :: else ->\
        if\
        :: num_lifts_invalid >= MAX_INVALID_LIFTS - 1 ->\
            fromRef[node_id]!liftValid(cur_lift);\
        :: else ->\
            if\
            :: true ->\
                fromRef[node_id]!liftValid(cur_lift);\
            :: true ->\
                fromRef[node_id]!liftInvalid(cur_lift);\
                invalid_lifts[num_lifts_invalid] = cur_lift.id;\
                num_lifts_invalid = num_lifts_invalid + 1;\
            fi\
        fi\
    fi}
//TODO:: refCheckLiftValidForLeader == refCheckValidForNode(0)
#define refCheckLiftValidForLeader {\
    printf("Ref Checking for Leader...\n");\
    leader_recv?checkLiftValidity(cur_lift);\
    for(j: 0 .. num_lifts_invalid){\
        if\
        :: invalid_lifts[j] == cur_lift.id ->\
            cur_lift_invalid = true;\
            printf("ref sending invalid response to leader\n");\
            leader_send!liftInvalid(cur_lift);\
            break;\
        :: else -> skip;\
        fi\
    }\
    if\
    :: cur_lift_invalid -> cur_lift_invalid = false;\
    :: else ->\
        if\
        :: num_lifts_invalid >= MAX_INVALID_LIFTS - 1 ->\
            printf("ref sending valid response to leader\n");\
            leader_send!liftValid(cur_lift);\
        :: else ->\
            if\
            :: true ->\
                printf("ref sending valid response to leader\n");\
                leader_send!liftValid(cur_lift);\
            :: true ->\
                printf("ref sending invalid response to leader\n");\
                leader_send!liftInvalid(cur_lift);\
                invalid_lifts[num_lifts_invalid] = cur_lift.id;\
                num_lifts_invalid = num_lifts_invalid + 1;\
            fi\
        fi\
    fi}
//INLINES
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
/*#define leaderHandleVerifiedLift(up_recv, cur_lift, lifts_completed, lift_in_progress) {\
    up_recv?verified_lift(cur_lift);\
    printf("success!\nLift_id: %d\nLift_val: %d\n\n", cur_lift.id, cur_lift.value);\
    lifts_completed = lifts_completed + 1;\
    printState();\
    if\
    :: lifts_completed == NUM_LIFTS -> break;\
    :: else -> skip;\
    fi\
    lift_in_progress = false;}
    */
inline leaderHandleVerifiedLift(up_recv, cur_lift, lifts_completed, lift_in_progress) {
    up_recv?verified_lift(cur_lift)
    printf("success!\nLift_id: %d\nLift_val: %d\n\n", cur_lift.id, cur_lift.value)
    lifts_completed = lifts_completed + 1
    printState()
    if
    :: lifts_completed == NUM_LIFTS ->
        break
    :: else -> skip
    fi
    lift_in_progress = false
}

proctype malNode(byte id) {
    bool lift_in_progress 
    byte payment_amt
    byte next
    byte prev
    chan up_send
    chan down_send
    chan up_recv
    chan down_recv
    byte payments_remaining
    chan to_ref
    chan from_ref
    byte invalid_lifts[MAX_INVALID_LIFTS]
    byte num_lifts_invalid
    bool cur_lift_invalid
    Lift cur_lift

        /*INITIALIZATION*/
    atomic
    {
        initializeNode(id, payment_amt, next, prev, up_send, down_send, up_recv, down_recv, payments_remaining, lift_in_progress, to_ref, from_ref, num_lifts_invalid, cur_lift_invalid) }
    /*************************/
    ALL_INITIALIZED
    do
    :: down_recv?<proposed_lift(cur_lift)> ->
        atomic{
            nodeHandleProposedLift(id, down_recv, down_send, cur_lift, lift_in_progress)
        }
        
    :: up_recv?<verified_lift(cur_lift)> ->
        atomic{
            malNodeHandleVerifiedLift(id, up_recv, cur_lift, up_send)
        }

    :: down_recv?<poison(_)> ->
        atomic{
            nodeHandlePoison(down_recv, down_send)
        }
    od
    printState()
}

proctype node(byte id) {
    
    Lift cur_lift
    bool lift_in_progress
    byte payment_amt
    byte next
    byte prev
    chan up_send
    chan down_send
    chan up_recv
    chan down_recv
    byte payments_remaining
    chan to_ref
    chan from_ref
    byte invalid_lifts[MAX_INVALID_LIFTS] = 0
    byte num_lifts_invalid
    bool cur_lift_invalid
    byte i = 0
        /*INITIALIZATION*/
    atomic
    {
        initializeNode(id, payment_amt, next, prev, up_send, down_send, up_recv, down_recv, payments_remaining, lift_in_progress, to_ref, from_ref, num_lifts_invalid, cur_lift_invalid)
    }
    /*************************/
    ALL_INITIALIZED
    do
    :: down_recv?<proposed_lift(cur_lift)> ->
        atomic{
            nodeHandleProposedLift(id, down_recv, down_send, cur_lift, lift_in_progress)
        }
        
    :: up_recv?<verified_lift(cur_lift)> ->
        atomic{
            nodeHandleVerifiedLift(id, cur_lift_invalid, num_lifts_invalid, invalid_lifts, cur_lift, up_recv, up_send, lift_in_progress)
        }

    :: down_recv?<poison(_)> ->
        atomic{
            nodeHandlePoison(down_recv, down_send)
        }
    :: lift_in_progress ->
        atomic{
            cur_lift_invalid = false
            for(i : 0 .. num_lifts_invalid){
                if
                :: invalid_lifts[i] == cur_lift.id -> 
                    cur_lift_invalid = true
                    break
                :: else -> skip
                fi
            }
            if
            :: cur_lift_invalid -> skip
            :: else ->
                to_ref!checkLiftValidity(cur_lift)
                if
                :: from_ref?<liftValid(cur_lift)> -> 
                    from_ref?liftValid(cur_lift)
                :: from_ref?<liftInvalid(cur_lift)> -> 
                    from_ref?liftInvalid(cur_lift)
                    invalid_lifts[num_lifts_invalid] = cur_lift.id
                    conditional[id] = conditional[id] - cur_lift.value
                    num_lifts_invalid = num_lifts_invalid + 1
                    lift_in_progress = false
                fi
            fi
        }
    od
    printState()

}

proctype leader(byte id) {
        /*INITIALIZATION*/
    Lift cur_lift
    byte payment_amt
    byte next
    byte prev
    chan up_send
    chan down_send
    chan up_recv
    chan down_recv
    chan to_ref
    chan from_ref
    byte lifts_remaining
    byte lifts_completed
    byte payments_remaining
    bool lift_in_progress
    bool cur_lift_invalid
    byte num_lifts_invalid
    byte invalid_lifts[MAX_INVALID_LIFTS] = 0
    byte i

    atomic{
        initializeLeader(id, payment_amt, next, prev, up_send, down_send, up_recv, down_recv, lifts_remaining, lifts_completed, payments_remaining, lift_in_progress, to_ref, from_ref)
    }
    /*************************/
    ALL_INITIALIZED
    do
    :: lifts_remaining > 0 && !lift_in_progress && next_lift_id <= MAX_INVALID_LIFTS - 1->
        atomic{
            printf("leader creating new lift: %d\n", next_lift_id)
            leaderSendProposedLift(down_send, lifts_remaining, lift_in_progress)
        }
    :: down_recv?<proposed_lift(cur_lift)> ->
        atomic{
            leaderHandleProposedLift(down_recv, cur_lift, to_ref, from_ref, up_send, lift_in_progress, lifts_remaining, num_lifts_invalid, invalid_lifts, cur_lift_invalid)
        }
    :: up_recv?<verified_lift(cur_lift)> ->
        atomic{
            leaderHandleVerifiedLift(up_recv, cur_lift, lifts_completed, lift_in_progress)
        }
    :: lift_in_progress ->
        atomic{
            cur_lift_invalid = false
            for(i : 0 .. num_lifts_invalid){
                if
                :: invalid_lifts[i] == cur_lift.id -> 
                    cur_lift_invalid = true
                    break
                :: else -> skip
                fi
            }
            if
            :: cur_lift_invalid -> skip
            :: else ->
                printf("Leader Requesting Ref Check (in main loop)...\n")
                to_ref!checkLiftValidity(cur_lift)
                if
                :: from_ref?<liftValid(cur_lift)> ->
                    from_ref?liftValid(cur_lift)
                :: from_ref?<liftInvalid(cur_lift)> ->
                    from_ref?liftInvalid(cur_lift)
                    invalid_lifts[num_lifts_invalid] = cur_lift.id
                    num_lifts_invalid = num_lifts_invalid + 1
                    conditional[id] = conditional[id] - cur_lift.value
                    lift_in_progress = false
                    lifts_remaining = lifts_remaining + 1
                fi
            fi
        }
    od
    Lift dummy
    dummy.value = 0
    dummy.id = 0
    down_send!poison(dummy)
    to_ref!poison(dummy)
    printState()
}

proctype referee(byte id){
    chan leader_recv
    chan leader_send
    byte invalid_lifts[MAX_INVALID_LIFTS] = 0
    byte num_lifts_invalid
    bool cur_lift_invalid
    byte j
    byte i
    Lift cur_lift

    atomic{
        leader_recv = toRef[0]
        leader_send = fromRef[0]
        num_lifts_invalid = 0
        cur_lift_invalid = false
        initialized[4] = true
    }
    ALL_INITIALIZED
    do
    :: leader_recv?<checkLiftValidity(cur_lift)> ->
        atomic{
            refCheckLiftValidForLeader
            cur_lift_invalid = false
        }
    :: toRef[1]?<checkLiftValidity(cur_lift)> ->
        atomic{
            refCheckLiftValidForNode(1)
        }
    :: toRef[2]?<checkLiftValidity(cur_lift)> ->
        atomic{
            refCheckLiftValidForNode(2)
        }
    :: toRef[3]?<checkLiftValidity(cur_lift)> ->
        atomic{
            refCheckLiftValidForNode(3)
        }
    :: leader_recv?<poison(_, _)> ->
        atomic{
            leader_recv?poison(_, _)
            break
        }
    od

}

init{
    atomic{
        run leader(0)
        run node(1)
        run node(2)
        run node(3)
        run referee(4)
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
ltl p2 {always eventually ABEqual && BCEqual && CDEqual && DAEqual}

#define AOverLift (foils[0] < 0)
#define BOverLift (foils[1] < 0)
#define COverLift (foils[2] < 0)
#define DOverLift (foils[3] < 0)

//There will never be an overlift
ltl p3 {always (!AOverLift && !BOverLift && !COverLift && !DOverLift)}

//Conditional values will always reach 0

