From Coq Require Import Bool.Bool.
From Coq Require Import Lists.List.
From Coq Require Import Lists.ListSet.
Import ListNotations.
From Coq Require Import ZArith.
From Coq Require Import ZArith.Int.


(*--------------------------------CHIT DEFINITIONS-----------------------------*)
Inductive chit_state : Type :=
  | Conditional (liftId : nat)
  | Valid.

Inductive chit : Type :=
  | Chit (value : Z) (state : chit_state).

Definition get_chit_value (c : chit) :=
  match c with
  | Chit value _ => value
  end.

Definition get_chit_state (c : chit) :=
  match c with
  | Chit _ state => state
  end.
                         
Notation "c '.value' "
  := (get_chit_value c)
  (at level 90, left associativity).

Notation "c '.state' "
  := (get_chit_state c)
  (at level 90, left associativity).

(* 
   It is impossible to know if a tally has reached consensus.
   We can only know that we have not reached consensus.
   But we do know that the sum of chits we do know about will be greater or equal to the 
   sum of all chits in the system
   Therefor consensus is not a property needed for the lifts contract
*)

(*--------------------------------Tally DEFINITIONS-----------------------------*)
Inductive stockOrFoil : Type :=
  | Stock
  | Foil.

Inductive tally : Type :=
  | Tally (chits : list chit) (type : stockOrFoil) (partnerID : nat).

Definition get_tally_chits (t : tally) :=
  match t with
  | Tally chits _ _ => chits
  end.

Definition get_tally_type (t : tally) :=
  match t with
  | Tally _ type _ => type
  end.

Definition get_tally_partnerID (t : tally) :=
  match t with
  | Tally _ _ id => id
  end.

Notation "t '.chits' "
  := (get_tally_chits t)
  (at level 90, left associativity).

Notation "t '.type' "
  := (get_tally_type t)
  (at level 90, left associativity).

Notation "t '.partnerID' "
  := (get_tally_partnerID t)
  (at level 90, left associativity).

Fixpoint committed_chits_sum (chits : list chit) : Z :=
  match chits with
  | nil => 0
  | chit :: t => match chit.state with
                 | Valid => chit.value + (committed_chits_sum t)
                 | Conditional LID => 0 + (committed_chits_sum t)
                 end 
  end.

Fixpoint conditional_chits_sum (chits : set chit) : Z :=
  match chits with
  | nil => 0
  | chit :: t => match chit.state with
                 | Valid => 0 + (conditional_chits_sum t)
                 | Conditional LID => chit.value + (conditional_chits_sum t)
                 end 
  end.

Notation "t '.committedTotal' "
  := (committed_chits_sum (t.chits))
  (at level 90, left associativity).

Notation "t '.conditionalTotal' "
  := (conditional_chits_sum (t.chits))
  (at level 90, left associativity).

(*--------------------------------Node DEFINITIONS-----------------------------*)

Inductive node : Type :=
  | Node (id : nat) (tallies : list tally).

Definition get_node_id (n : node) :=
  match n with
  | Node id _ => id
  end.

Definition get_node_tallies (n : node) :=
  match n with
  | Node _ tallies => tallies
  end.

Notation "n '.id' "
  := (get_node_id n)
  (at level 90, left associativity).

Notation "n '.tallies' "
  := (get_node_tallies n)
  (at level 90, left associativity).

(* A method to determine if two nodes are equal. They are equal if they have the same name. *)
Definition eqb (m n : node) : bool :=
  match m with
  | Node m' _ => match n with
               | Node n' _ => (m' =? n')
               end
  end.

(* Finds the index of a node within a list of nodes. Often a list of nodes represents a cycle *)
Fixpoint indexOf (n : node) (cycle : list node) : (option nat) :=
  match cycle with
  | [] => None
  | m :: cycle' => if eqb m n then Some 0
                  else match (indexOf n cycle') with
                  | Some n => Some (S n)
                  | None => None
                  end
  end.

(*A method to find the next node in a cycle given the name of a starting node *)
Definition nextNode (n : node) (cycle : list node) : (option node) :=
  match (indexOf n cycle) with
  | None => None
  | Some a => if Nat.eqb (List.length cycle) (S a) then (nth_error cycle 0) else nth_error cycle (S a)
  end.

(* A method to find the previous node in a cycle given the name of a starting node *)
Definition prevNode (n : node) (cycle : list node) : (option node) :=
  match (indexOf n cycle) with
  | None => None
  | Some a => match a with
              | O => (nth_error cycle (List.length cycle - 1))
              | S a' => nth_error cycle a'
              end
  end.

Fixpoint tallyFor (nodeID : nat) (tallies : list tally) : option tally :=
  match tallies with
  | nil => None
  | tally :: tail => match tally with
                     | Tally _ _ id => if id =? nodeID then Some tally else None
                     end
  end.

Notation "t '[[' i ']]'"
  := (tallyFor i t)
  (at level 90, left associativity).

