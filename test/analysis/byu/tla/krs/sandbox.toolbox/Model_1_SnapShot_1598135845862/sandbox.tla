------------------------------ MODULE sandbox ------------------------------
EXTENDS Naturals, TLC

(* --algorithm transfer
variables alice_account = 10, bob_account = 10, money \in 1..20,
    account_total = alice_account + bob_account;

begin
Transfer:
    if alice_account >= money then
        A: alice_account := alice_account - money;
           bob_account := bob_account + money;
    end if;
    C: assert alice_account >= 0;

end algorithm *)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-02a8c3398090097994c659e182e3b5b6
VARIABLES alice_account, bob_account, money, account_total, pc

vars == << alice_account, bob_account, money, account_total, pc >>

Init == (* Global variables *)
        /\ alice_account = 10
        /\ bob_account = 10
        /\ money \in 1..20
        /\ account_total = alice_account + bob_account
        /\ pc = "Transfer"

Transfer == /\ pc = "Transfer"
            /\ IF alice_account >= money
                  THEN /\ pc' = "A"
                  ELSE /\ pc' = "C"
            /\ UNCHANGED << alice_account, bob_account, money, account_total >>

A == /\ pc = "A"
     /\ alice_account' = alice_account - money
     /\ bob_account' = bob_account + money
     /\ pc' = "C"
     /\ UNCHANGED << money, account_total >>

C == /\ pc = "C"
     /\ Assert(alice_account >= 0, 
               "Failure of assertion at line 14, column 8.")
     /\ pc' = "Done"
     /\ UNCHANGED << alice_account, bob_account, money, account_total >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Transfer \/ A \/ C
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-c30104708ffb2bddf67671ce7f53b3ef

MoneyNotNegative == money >= 0
MoneyInvarient == alice_account + bob_account = account_total

=============================================================================
\* Modification History
\* Last modified Sat Aug 22 16:37:20 MDT 2020 by kylestorey
\* Created Sat Aug 22 16:05:32 MDT 2020 by kylestorey
