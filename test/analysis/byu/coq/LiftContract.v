From Coq Require Import Bool.Bool.
From Coq Require Import Lists.List.
From Coq Require Import Lists.ListSet.
Import ListNotations.
From Coq Require Import ZArith.
From Coq Require Import ZArith.Int.
Require Import MyChipsDefinitions.

Compute committed_chits_sum [(Chit 1 Valid) ; (Chit 1 Valid) ; (Chit 4 Valid)].
Compute (Tally [(Chit 7 Valid) ; (Chit 1 Valid) ; (Chit 4 Valid)] Stock 0).committedTotal.
Compute (Tally [(Chit 7 (Conditional 0)) ; (Chit (-3) Valid) ; (Chit 5 Valid)] Stock 1).committedTotal.
Compute (Tally [(Chit 1 Valid) ; (Chit 4 Valid) ; (Chit 7 (Conditional 3))] Foil 2).conditionalTotal.
Compute ((Node 0 [(Tally [(Chit 1 Valid) ; (Chit 7 (Conditional 3))] Foil 2)]).id).
Compute (Node 0 [(Tally [(Chit 1 Valid) ; (Chit 7 (Conditional 3))] Foil 2)]).tallies[[2]].
Compute (Node 0 [(Tally [(Chit 1 Valid) ; (Chit 7 (Conditional 3))] Foil 2)]).tallies[[1]].


