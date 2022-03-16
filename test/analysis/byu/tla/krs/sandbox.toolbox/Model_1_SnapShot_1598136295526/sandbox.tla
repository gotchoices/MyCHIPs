------------------------------ MODULE sandbox ------------------------------
EXTENDS Naturals, TLC

(* --algorithm transfer
variables alice_account = 10, bob_account = 10,
          account_total = alice_account + bob_account;

process Transfer \in 1..2
  variable money \in 1..20;
begin
Transfer:
  if alice_account >= money then
    A: alice_account := alice_account - money;
       bob_account := bob_account + money;
end if;
end process

end algorithm *)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-bc355e3bb03b78eac82071f8a720b6b3
\* Label Transfer of process Transfer at line 12 col 3 changed to Transfer_
VARIABLES alice_account, bob_account, account_total, pc, money

vars == << alice_account, bob_account, account_total, pc, money >>

ProcSet == (1..2)

Init == (* Global variables *)
        /\ alice_account = 10
        /\ bob_account = 10
        /\ account_total = alice_account + bob_account
        (* Process Transfer *)
        /\ money \in [1..2 -> 1..20]
        /\ pc = [self \in ProcSet |-> "Transfer_"]

Transfer_(self) == /\ pc[self] = "Transfer_"
                   /\ IF alice_account >= money[self]
                         THEN /\ pc' = [pc EXCEPT ![self] = "A"]
                         ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                   /\ UNCHANGED << alice_account, bob_account, account_total, 
                                   money >>

A(self) == /\ pc[self] = "A"
           /\ alice_account' = alice_account - money[self]
           /\ bob_account' = bob_account + money[self]
           /\ pc' = [pc EXCEPT ![self] = "Done"]
           /\ UNCHANGED << account_total, money >>

Transfer(self) == Transfer_(self) \/ A(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in 1..2: Transfer(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-ada34c383b475c746e3e3f71643d3f58

MoneyNotNegative == money >= 0
MoneyInvariant == alice_account + bob_account = account_total

=============================================================================
\* Modification History
\* Last modified Sat Aug 22 16:44:47 MDT 2020 by kylestorey
\* Created Sat Aug 22 16:05:32 MDT 2020 by kylestorey
