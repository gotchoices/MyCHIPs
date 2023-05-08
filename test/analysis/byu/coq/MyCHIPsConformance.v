(*
   A proof that a chain of n+1 relay nodes in the MyCHIPs credit lift protocol conforms to a chain of n relay nodes. This is utilized as part of an inductive step that showes that safety and liveness properties in a small system continue to hold in a credit lift with any number of nodes.
*)

Require Import List.
Import ListNotations. (*Make lists comfy to use*)
Import Bool. (*Some true or false would be nice*)
Require Import Psatz. (* Give me lia please *)
Require Import ZArith_base. (*I'll need some integers*)

Infix "mod" := Z.modulo (at level 40, no associativity).

Module Conformance.

  Inductive Message :=
    | Promise
    | Commit.

  Inductive Action :=
    | Send (src : Z) (dest : Z) (m : Message)
    | Receive (dest : Z) (m : Message)
    | SendRef (src : Z)
    | ReceiveRef (dest : Z).

  Definition isReceive (a : Action) := match a with
                                    | Receive _ _ => True
                                    | _ => False
                                    end.

  Definition isReceiveRef (a : Action) := match a with
                                    | ReceiveRef _ => True
                                    | _ => False
                                    end.
  Definition isSendRef (a : Action) := match a with
                                    | SendRef _ => True
                                    | _ => False
                                    end.

  
  (*
     We would like to show that certain properties hold before and after projection:

     We have all the required actions and only the required actions for the MyCHIPS Protocol
     Those actions occur in the correct order.

   *)

  Definition has_required_actions (acts : list Action) (size : nat) :=
    (
      exists (m : nat),
      forall (n : nat),
      ((n >= m) -> ((S n) < size) ->
      In (Send (Z.of_nat (S n)) (Z.of_nat n) Commit) acts /\
      In (Receive (Z.of_nat (n)) Commit) acts 
      ) 
      /\ 
      ((n < m) -> (n < size) ->
      In (SendRef (Z.of_nat (n))) acts /\
      In (ReceiveRef (Z.of_nat (n))) acts
      ) 
    )
    /\
    (
    forall (n : nat),
    (S n) < size -> (*Note strictly less then size means promise to Originator is not required*)
    In (Send (Z.of_nat (n)) (Z.of_nat (S n)) Promise) acts /\
    In (Receive (Z.of_nat (n)) Promise) acts
    ).
  (*Consider if last requirement should be true only if there exists a commit send or receive*)

  Ltac recursive_try_reflexivity := (repeat left+right); reflexivity.

  Example hra_1 : has_required_actions [(Send 0 1 Promise) ; (Receive 1 Promise) ; (Send 1 2 Promise) ; (Receive 0 Promise) ; (Send 0 (-1) Commit) ; (Receive 1 Commit) ; (Send 1 0 Commit) ; (Receive 0 Commit)] 2.
  Proof.
    unfold has_required_actions.
    split.
    exists 0.
    intros.
    split.
    intros.
    destruct n.
    split.
    recursive_try_reflexivity.
    recursive_try_reflexivity.
    lia.
    intros.
    lia.
    split.
    intros.
    destruct n.
    recursive_try_reflexivity.
    destruct n.
    recursive_try_reflexivity.
    lia.
    destruct n.
    recursive_try_reflexivity.
    lia.
  Qed.

  Lemma action_equal_decidable : forall x y : Action, {x = y}+{x <> y}.
    Proof.
      intros.
      destruct x, y.
      destruct m, m0; try (right; discriminate).
      --
      pose proof (Z.eq_dec src src0).
      destruct H.
      pose proof (Z.eq_dec dest dest0).
      destruct H.
      left.
      rewrite e, e0.
      reflexivity.
      right.
      auto.
      red.
      intros.
      inversion H.
      contradiction.
      right.
      red.
      intros.
      inversion H.
      contradiction.
      --
      pose proof (Z.eq_dec src src0).
      destruct H.
      pose proof (Z.eq_dec dest dest0).
      destruct H.
      left.
      rewrite e.
      rewrite e0.
      reflexivity.
      right.
      red.
      intros.
      inversion H.
      contradiction.
      right.
      red.
      intros.
      inversion H.
      contradiction.
      --
      right.
      discriminate.
      --
      right.
      discriminate.
      --
      right.
      discriminate.
      --
      right.
      discriminate.
      --
      destruct m, m0.
      pose proof (Z.eq_dec dest dest0).
      destruct H.
      left.
      rewrite e.
      reflexivity.
      right.
      red.
      intros.
      inversion H.
      contradiction.
      right.
      discriminate.
      right.
      discriminate.
      pose proof (Z.eq_dec dest dest0).
      destruct H.
      left.
      rewrite e.
      reflexivity.
      right.
      red.
      intros.
      inversion H.
      contradiction.
      --
      right.
      discriminate.
      --
      right.
      discriminate.
      --
      right.
      discriminate.
      --
      right.
      discriminate.
      --
      pose proof (Z.eq_dec src src0).
      destruct H.
      left.
      rewrite e.
      reflexivity.
      right.
      red.
      intros.
      inversion H.
      contradiction.
      --
      right.
      discriminate.
      --
      right.
      discriminate.
      --
      right.
      discriminate.
      --
      right.
      discriminate.
      --
      pose proof (Z.eq_dec dest dest0).
      destruct H.
      left.
      rewrite e.
      reflexivity.
      right.
      red.
      intros.
      inversion H.
      contradiction.
    Qed.

  Definition count_occ_action := count_occ action_equal_decidable.

  Definition has_no_duplicate_receives (acts : list Action) :=
    forall (a : Action), In a acts -> isReceive(a) -> count_occ_action acts a <= 1.

  Definition has_no_duplicate_actions (acts : list Action) :=
    forall (a : Action), In a acts -> count_occ_action acts a <= 1.

  Definition node_eq (a b : Z) (size : nat) := (a mod (Z.of_nat size)) = (b mod (Z.of_nat size)).

  Definition is_send_for_receive (s : Action) (r : Action) (size : nat) :=
    match s with
    | Send src_s dest_s m_s => match r with
                                | Receive dest_r m_r => node_eq dest_s dest_r size /\ m_s = m_r
                                | _ => False
                               end
    | _ => False
    end.

  Fixpoint happens_before (x : Action) (y : Action) (acts : list Action) :=
    match acts with
    | [] => False
    | a :: acts' => a = x \/ (a <> x /\ a <> y /\ (happens_before x y acts'))
    end.

  Definition all_receives_causal (acts : list Action) (size : nat) := forall (r : Action), isReceive r /\ In r acts -> exists (a : Action), In a acts /\ happens_before a r acts /\ (is_send_for_receive a r size).

  Definition is_sendRef_for_receiveRef (s : Action) (r : Action) :=
    match s with
    | SendRef src_s => match r with
                                | ReceiveRef dest_r => src_s = dest_r                                | _ => False
                               end
    | _ => False
    end.

  Definition all_ref_receives_causal (acts : list Action) (size : nat) := forall (r : Action), isReceiveRef r /\ In r acts -> exists (a : Action), In a acts /\ happens_before a r acts /\ is_sendRef_for_receiveRef a r.

  Definition all_sends_triggered (acts : list Action) :=
    forall (src dest : Z) (m : Message),
    src <> 0%Z /\ In (Send src dest m) acts ->
    In (Receive src m) acts /\ happens_before (Receive src m) (Send src dest m) acts.

  Definition all_ids_in_range (acts : list Action) (size : nat) :=
    forall (a : Action), In a acts -> match a with
                                     | Send src dest m => (0 <= src < (Z.of_nat size))%Z /\ (-1 <= dest <= (Z.of_nat size))%Z
                                     | Receive dest m => (0 <= dest < (Z.of_nat size))%Z
                                     | SendRef src => (0 <= src < (Z.of_nat size))%Z
                                     | ReceiveRef dest => (0 <= dest < (Z.of_nat size))%Z
                                     end.

  Definition promise_forward_commit_backward (acts : list Action) := 
    forall (a : Action),
    In a acts ->
    match a with
    | Send src dest Promise => (dest = (src + 1)%Z)
    | Send src dest Commit => ((dest + 1)%Z = src)
    | _ => True
    end.


  Definition phase_sequence_correct (acts : list Action) :=
    forall (a b : Action),
    In a acts -> In b acts ->
    match a with
    | Send 0 (-1) Commit => match b with 
                            | Send 0 (-1) Commit => True
                            | Send _ _ Commit => happens_before a b acts
                            | Receive _ Commit => happens_before a b acts
                            | _ => True
                            end
    | Send _ _ _ => True
    | Receive 0 m => match b with
                           | Send _ _ m => happens_before b a acts
                           | _ => True
                           end
    | SendRef s => match b with
                   |  Send s _ Promise => happens_before b a acts
                   |  Receive s Commit => happens_before a b acts
                   | _ => True
                   end
    | _ => True
    end.

  Definition acts_valid (acts : list Action) (size : nat) :=
    size > 1 /\
    has_required_actions acts size /\
    has_no_duplicate_receives acts /\
    (*has_no_duplicate_actions acts /\*)
    all_receives_causal acts size /\
    all_sends_triggered acts /\ 
    all_ids_in_range acts size /\
    promise_forward_commit_backward acts /\
    phase_sequence_correct acts /\
    all_ref_receives_causal acts size.

  Example basic_size_3_trace_valid : acts_valid [(Send 0 1 Promise) ; (Receive 1 Promise) ; (Send 1 2 Promise) ; (Receive 2 Promise) ; (Send 2 3 Promise) ; (Receive 0 Promise) ; (Send 0 (-1) Commit); (Receive 2 Commit); (Send 2 1 Commit) ; (Receive 1 Commit) ; (Send 1 0 Commit) ; (Receive 0 Commit)] 3.
  Proof.
    unfold acts_valid.
    split.
    lia.
    split.
    unfold has_required_actions.
    split.
    exists 0.
    split.
    intros.
    split.
    simpl.
    destruct n.
    recursive_try_reflexivity.
    destruct n.
    recursive_try_reflexivity.
    lia.
    destruct n.
    recursive_try_reflexivity.
    destruct n.
    recursive_try_reflexivity.
    lia.
    intros.
    lia.
    split.
    intros.
    destruct n.
    recursive_try_reflexivity.
    destruct n.
    recursive_try_reflexivity.
    lia.
    destruct n.
    recursive_try_reflexivity.
    destruct n.
    recursive_try_reflexivity.
    lia.
    split.
    admit.
    split.
    unfold all_receives_causal.
    intros.
    destruct H.
    simpl in H0.
    destruct H0; try rewrite <- H0 in H; try discriminate; try contradiction.
    destruct H0; try rewrite <- H0 in H; try discriminate; try contradiction.
    exists (Send 0 1 Promise).
    split.
    simpl.
    recursive_try_reflexivity.
    rewrite <- H0.
    simpl.
    split.
    recursive_try_reflexivity.
    split.
    unfold node_eq.
    reflexivity.
    reflexivity.
    destruct H0; try rewrite <- H0 in H; try discriminate; try contradiction.
    destruct H0; try rewrite <- H0 in H; try discriminate; try contradiction.
    exists (Send 1 2 Promise).
    split.
    simpl.
    recursive_try_reflexivity.
    rewrite <- H0.
    simpl.
    split; try right; try split; try discriminate.
    split; try right; try split; try discriminate.
    split.
    discriminate.
    left.
    reflexivity.
    reflexivity.
    reflexivity.
    destruct H0; try rewrite <- H0 in H; try discriminate; try contradiction.
    destruct H0; try rewrite <- H0 in H; try discriminate; try contradiction.
    exists (Send 2 3 Promise).
    split.
    simpl.
    recursive_try_reflexivity.
    rewrite <- H0.
    simpl.
    split; try right; try split; try discriminate.
    split; try right; try split; try discriminate.
    split; try right; try split; try discriminate.
    split; try right; try split; try discriminate.
    split.
    discriminate.
    left.
    reflexivity.
    reflexivity.
    reflexivity.
    destruct H0; try rewrite <- H0 in H; try discriminate; try contradiction.
    destruct H0; try rewrite <- H0 in H; try discriminate; try contradiction.
    exists (Send 0 (-1) Commit).
    split.
    simpl.
    recursive_try_reflexivity.
    rewrite <- H0.
    simpl.
    split; try right; try split; try discriminate.
    split; try right; try split; try discriminate.
    split; try right; try split; try discriminate.
    split; try right; try split; try discriminate.
    split; try right; try split; try discriminate.
    split; try right; try split; try discriminate.
    split.
    discriminate.
    left.
    reflexivity.
    reflexivity.
    reflexivity.
    destruct H0; try rewrite <- H0 in H; try discriminate; try contradiction.
    destruct H0; try rewrite <- H0 in H; try discriminate; try contradiction.
    exists (Send 2 1 Commit).
    split.
    simpl.
    recursive_try_reflexivity.
    rewrite <- H0.
    simpl.
    split; try right; try split; try discriminate.
    split; try right; try split; try discriminate.
    split; try right; try split; try discriminate.
    split; try right; try split; try discriminate.
    split; try right; try split; try discriminate.
    split; try right; try split; try discriminate.
    split; try right; try split; try discriminate.
    split; try right; try split; try discriminate.
    split.
    discriminate.
    left.
    reflexivity.
    reflexivity.
    reflexivity.
    destruct H0; try rewrite <- H0 in H; try discriminate; try contradiction.
    destruct H0; try rewrite <- H0 in H; try discriminate; try contradiction.
    exists (Send 1 0 Commit).
    split.
    simpl.
    recursive_try_reflexivity.
    rewrite <- H0.
    simpl.
    split; try right; try split; try discriminate.
    split; try right; try split; try discriminate.
    split; try right; try split; try discriminate.
    split; try right; try split; try discriminate.
    split; try right; try split; try discriminate.
    split; try right; try split; try discriminate.
    split; try right; try split; try discriminate.
    split; try right; try split; try discriminate.
    split; try right; try split; try discriminate.
    split; try right; try split; try discriminate.
    split.
    discriminate.
    left.
    reflexivity.
    reflexivity.
    reflexivity.
  Admitted.

    
    

  Definition projected (size : nat) (act : Action) : option Action :=
    match act with
      | Send src dest m => 
          if (Z_le_dec (Z.of_nat size) src) then None
          else if (Z_lt_dec (Z.of_nat size) dest) then None
          else Some act
      | Receive dest m => 
          if (Z_le_dec (Z.of_nat size) dest)
          then None
          else Some act
      | ReceiveRef dest => 
          if (Z_le_dec (Z.of_nat size) dest)
          then None
          else Some act
      | SendRef src => 
          if (Z_le_dec (Z.of_nat size) src)
          then None
          else Some act
    end.


  Lemma projected_in_or_out : forall (size : nat) (act : Action), projected size act = Some act \/ projected size act = None.
    Proof.
      intros.
      unfold projected.
      destruct act.
      destruct (Z_le_dec (Z.of_nat size) src);
      destruct (Z_lt_dec (Z.of_nat size) dest);
      recursive_try_reflexivity.
      destruct (Z_le_dec (Z.of_nat size) dest);
      recursive_try_reflexivity.
      destruct (Z_le_dec (Z.of_nat size) src);
      recursive_try_reflexivity.
      destruct (Z_le_dec (Z.of_nat size) dest);
      recursive_try_reflexivity.
    Qed.

  Definition in_projection (size : nat) (act : Action) :=
    match projected size act with
    | Some _ => True
    | None => False
    end.

  Fixpoint project_to_size (size : nat) (acts : list Action) : list Action :=
    match acts with
    | [] => []
    | act :: acts' => match (projected size act) with
                      | Some a => a :: (project_to_size size acts')
                      | None => (project_to_size size acts')
                      end
    end.

  Definition exampleList := [(Send 0 (-1) Commit); (Receive 2 Commit); (Send 2 1 Commit) ; (Receive 1 Commit) ; (Send 1 0 Commit)].

  Example project1 : project_to_size 2 exampleList = [(Send 0 (-1) Commit); (Receive 1 Commit) ; (Send 1 0 Commit)].
  Proof.
    simpl.
    reflexivity.
  Qed.

  Lemma in_projection_remains : forall (acts : list Action) (a : Action) (size : nat), In a acts /\ in_projection size a <-> In a (project_to_size size acts).
  Proof.
    split.
    -
      intros.
      induction acts.
      destruct H as [InActs InProjection].
      inversion InActs.
      simpl.
      destruct H as [InActs InProjection].
      pose proof (projected_in_or_out size a0) as Hproja0.
      destruct Hproja0 as [ProjIn | ProjOut].
      rewrite ProjIn.
      simpl.
      simpl in InActs.
      destruct InActs as [a0eq | InActs].
      left.
      assumption.
      right.
      apply IHacts.
      split; assumption.
      simpl in InActs.
      destruct InActs as [a0eq | InActs].
      unfold in_projection in InProjection.
      rewrite <- a0eq in InProjection.
      rewrite ProjOut in InProjection.
      contradiction.
      rewrite ProjOut.
      apply IHacts.
      split; assumption.
    -
      intros.
      induction acts.
      contradiction.
      simpl in H.
      pose proof (projected_in_or_out size a0).
      destruct H0 as [ProjIn | ProjOut].
      rewrite ProjIn in H.
      simpl.
      simpl in H.
      destruct H as [a0eq | InProjection].
      split.
      left.
      assumption.
      unfold in_projection.
      rewrite <- a0eq.
      rewrite ProjIn.
      trivial.
      assert (In a acts /\ in_projection size a).
      apply IHacts.
      assumption.
      destruct H as [InActs InProj].
      split.
      right.
      assumption.
      assumption.
      rewrite ProjOut in H.
      simpl.
      assert (In a acts /\ in_projection size a).
      apply IHacts.
      assumption.
      destruct H0.
      split.
      right.
      assumption.
      assumption.
  Qed.

  Lemma in_proj_in_orig : forall (acts : list Action) (a : Action) (size : nat), In a (project_to_size size acts) ->  In a acts.
  Proof.
    intros.
    apply in_projection_remains in H.
    destruct H.
    assumption.
  Qed.

  Lemma not_in_orig_not_in_proj : forall (acts : list Action) (a : Action) (size : nat), ~In a acts -> ~In a (project_to_size size acts).
  Proof.
    intros.
    induction acts.
    simpl.
    trivial.
    simpl.
    simpl in H.
    red in H.
    pose proof (projected_in_or_out size a0).
    destruct H0.
    rewrite H0.
    simpl.
    red.
    intros.
    apply H.
    destruct H1.
    left.
    apply H1.
    right.
    apply in_proj_in_orig with (size := size).
    assumption.
    rewrite H0.
    apply IHacts.
    red.
    intros.
    apply H.
    right.
    assumption.
  Qed.

  Lemma has_required_actions_independent_of_proj : forall (acts : list Action) (n : nat), has_required_actions acts (S n) /\ n > 1 -> has_required_actions (project_to_size n acts) n.
    Proof.
      intros.
      destruct H as [H Hng2].
      unfold has_required_actions in H.
      destruct H.
      unfold has_required_actions.
      split.
      destruct H.
      +
      exists x.
      intros.
      split.
      ++
      pose proof (H n0).
      intros.
      assert (S n0 < S n).
      lia.
      destruct H1.
      pose proof (H1 H2).
      pose proof H6 H4.
      destruct H7.
      split.
      apply in_projection_remains.
      split.
      assumption.
      unfold in_projection.
      simpl.
      destruct (Z_le_dec (Z.of_nat n) (Z.pos (Pos.of_succ_nat n0))).
      lia.
      destruct (Z_lt_dec (Z.of_nat n) (Z.of_nat n0)).
      lia.
      trivial.
      apply in_projection_remains.
      split.
      assumption.
      unfold in_projection.
      destruct n.
      lia.
      destruct n.
      lia.
      unfold projected.
      destruct Z_le_dec.
      lia.
      trivial.
      ++
      intros.
      pose proof (H n0).
      destruct H3.
      pose proof (H4 H1).
      assert (n0 < S n).
      lia.
      pose proof (H5 H6).
      destruct H7.
      split.
      apply in_projection_remains.
      split.
      assumption.
      unfold in_projection.
      destruct n.
      lia.
      destruct n.
      lia.
      simpl.
      destruct Z_le_dec.
      lia.
      trivial.
      apply in_projection_remains.
      split.
      assumption.
      unfold in_projection.
      destruct n.
      lia.
      destruct n.
      lia.
      simpl.
      destruct Z_le_dec.
      lia.
      trivial.
      +
      split.
      intros.
      apply in_projection_remains.
      split.
      assert (S n0 < S n).
      lia.
      pose proof H0 n0 H2.
      destruct H3.
      assumption.
      unfold in_projection.
      simpl.
      destruct Z_le_dec; try lia.
      destruct Z_lt_dec; try lia.
      assert (S n0 < S n).
      lia.
      pose proof H0 n0 H2.
      destruct H3.
      apply in_projection_remains.
      split.
      assumption.
      unfold in_projection.
      simpl.
      destruct Z_le_dec; try lia.
    Qed.

  Lemma has_no_duplicate_receives_independent_of_proj : forall (acts : list Action) (n : nat), has_no_duplicate_receives acts -> has_no_duplicate_receives (project_to_size n acts).
    Proof.
      unfold has_no_duplicate_receives in *.
      intros.
      induction acts.
      simpl.
      lia.
      simpl.
      pose proof projected_in_or_out n a0.
      destruct H2.
      rewrite H2.
      simpl.
      destruct action_equal_decidable.
      -
        assert (count_occ_action (project_to_size n acts) a = 0).
        pose proof (H a).
        rewrite e in H2.
        simpl in H3.
        destruct action_equal_decidable; try contradiction.
        assert (S (count_occ_action acts a) <= 1).
        apply H3.
        left.
        assumption.
        assumption.
        inversion H4.
        rewrite H6.
        apply count_occ_not_In.
        unfold count_occ_action in H6.
        apply count_occ_not_In in H6.
        apply not_in_orig_not_in_proj.
        assumption.
        lia.
        rewrite H3.
        lia.
      -
        apply IHacts.
        simpl in H.
        intros.
        pose proof (H a1).
        destruct H5; try contradiction.
        right.
        assumption.
        assumption.
        destruct (action_equal_decidable); lia.
        destruct (action_equal_decidable) in l; lia.
        simpl in H0.
        rewrite H2 in H0.
        simpl in H0.
        destruct H0; try contradiction.
        assumption.
      -
        rewrite H2.
        apply IHacts.
        simpl in H.
        intros.
        pose proof H a1.
        destruct action_equal_decidable in H5.
        assert (S (count_occ_action acts a1) <= 1).
        apply H5.
        left.
        assumption.
        assert (S (count_occ_action acts a1) <= 1).
        apply H5.
        right.
        assumption.
        assumption.
        assumption.
        lia.
        assert ((count_occ_action acts a1) <= 1).
        apply H5.
        right.
        assumption.
        assumption.
        simpl in H0.
        assumption.
        simpl in H0.
        rewrite H2 in H0.
        assumption.
    Qed.

  Lemma has_no_duplicate_actions_independent_of_proj : forall (acts : list Action) (n : nat), has_no_duplicate_actions acts -> has_no_duplicate_actions (project_to_size n acts).
    Proof.
      unfold has_no_duplicate_actions in *.
      intros.
      induction acts.
      simpl.
      lia.
      simpl.
      pose proof projected_in_or_out n a0.
      destruct H1.
      rewrite H1.
      simpl.
      destruct action_equal_decidable.
      -
        assert (count_occ_action (project_to_size n acts) a = 0).
        pose proof (H a).
        rewrite e in H1.
        simpl in H2.
        destruct action_equal_decidable; try contradiction.
        assert (S (count_occ_action acts a) <= 1).
        apply H2.
        left.
        assumption.
        inversion H3.
        rewrite H5.
        apply count_occ_not_In.
        unfold count_occ_action in H5.
        apply count_occ_not_In in H5.
        apply not_in_orig_not_in_proj.
        assumption.
        lia.
        rewrite H2.
        lia.
      -
        apply IHacts.
        simpl in H.
        intros.
        pose proof (H a1).
        destruct H3; try contradiction.
        right.
        assumption.
        destruct (action_equal_decidable); lia.
        destruct (action_equal_decidable) in l; lia.
        simpl in H0.
        rewrite H1 in H0.
        simpl in H0.
        destruct H0; try contradiction.
        assumption.
      -
        rewrite H1.
        apply IHacts.
        simpl in H.
        intros.
        pose proof H a1.
        destruct action_equal_decidable in H3.
        assert (S (count_occ_action acts a1) <= 1).
        apply H3.
        left.
        assumption.
        assert (S (count_occ_action acts a1) <= 1).
        apply H3.
        right.
        assumption.
        lia.
        assert ((count_occ_action acts a1) <= 1).
        apply H3.
        right.
        assumption.
        assumption.
        simpl in H0.
        rewrite H1 in H0.
        assumption.
    Qed.

  Lemma happens_before_independent_of_proj : forall (acts : list Action) (size : nat) (x : Action) (y : Action), happens_before x y acts /\ In x (project_to_size size acts) /\ In y (project_to_size size acts) -> happens_before x y (project_to_size size acts).
  Proof.
    intros.
    destruct H.
    destruct H0.
    rewrite <- in_projection_remains in H0, H1.
    induction acts.
    simpl in H.
    contradiction.
    simpl in H.
    destruct H.
    simpl.
    destruct H0.
    rewrite <- H in H2.
    unfold in_projection in H2.
    pose proof projected_in_or_out size a.
    destruct H3.
    rewrite H3.
    simpl.
    left.
    assumption.
    rewrite H3 in H2.
    contradiction.
    simpl.
    pose proof projected_in_or_out size a.
    assert (happens_before x y (project_to_size size acts)).
      apply IHacts.
      destruct H.
      destruct H3.
      assumption.
      split.
      destruct H0.
      simpl in H0.
      destruct H0.
      destruct H.
      contradiction.
      assumption.
      destruct H0.
      assumption.
      split.
      destruct H1.
      simpl in H1.
      destruct H.
      destruct H1.
      destruct H4.
      contradiction.
      assumption.
      destruct H1.
      assumption.
    destruct H2.
    rewrite H2.
    simpl.
    right.
    split.
    destruct H.
    assumption.
    split.
    destruct H.
    destruct H4.
    assumption.
    assumption.
    rewrite H2.
    assumption.
  Qed.


    Lemma modulo_small_equal : forall (a b m : Z), (0 <= a < m)%Z -> (0 <= b < m)%Z -> a mod m = b mod m -> a = b.
    Proof.
      intros.
      pose proof Zdiv.Zmod_small a m.
      pose proof H2 H.
      pose proof Zdiv.Zmod_small b m.
      pose proof H4 H0.
      rewrite H3 in H1.
      rewrite H5 in H1.
      assumption.
    Qed.

    Lemma all_ids_in_range_independent_of_proj : forall (acts : list Action) (n : nat), all_ids_in_range acts (S n) -> all_ids_in_range (project_to_size n acts) n.
    Proof.
      intros.
      unfold all_ids_in_range.
      intros.
      rewrite <- in_projection_remains in H0.
      destruct H0.
      unfold in_projection in H1.
      destruct a.
      simpl in H1.
      destruct (Z_le_dec (Z.of_nat n) src).
      contradiction.
      pose proof H (Send src dest m) H0.
      simpl in H2.
      split.
      lia.
      destruct (Z_lt_dec (Z.of_nat n) dest); try contradiction.
      lia.
      simpl in H1.
      destruct Z_le_dec.
      contradiction.
      pose proof H (Receive dest m) H0.
      simpl in H2.
      lia.
      unfold projected in H1.
      destruct (Z_le_dec (Z.of_nat n) src); try contradiction.
      assert (src < (Z.of_nat n))%Z.
      lia.
      unfold all_ids_in_range in H.
      pose proof H (SendRef src) H0.
      simpl in H3.
      lia.
      unfold all_ids_in_range in H.
      pose proof H (ReceiveRef dest) H0.
      simpl in H2.
      unfold projected in H1.
      destruct (Z_le_dec (Z.of_nat n) dest); try contradiction.
      assert (dest < (Z.of_nat n))%Z.
      lia.
      lia.
    Qed.

    Lemma promise_forward_commit_backward_independent_of_proj : forall (acts : list Action) (n : nat), promise_forward_commit_backward acts -> promise_forward_commit_backward (project_to_size n acts).
    Proof.
      intros.
      unfold promise_forward_commit_backward.
      intros.
      pose proof in_proj_in_orig acts a n H0.
      pose proof H a H1.
      destruct a;
      try destruct m;
      assumption.
    Qed.

    Lemma mod_minus_one : forall (n : nat), (n > 1) -> (-1) mod (Z.of_nat n) = ((Z.of_nat n)-1) mod Z.of_nat n.
    Proof.
      intros.
      destruct n.
      lia.
      destruct n.
      lia.
      remember (Z.of_nat (S (S n))) as m.
      assert (m > 0)%Z.
      lia.
      pose proof Zdiv.Z_mod_plus (-1) 1 m H0.
      assert ((-1 + 1 * m)%Z = (m - 1)%Z).
      lia.
      symmetry in H1.
      rewrite H2 in H1.
      assumption.
    Qed.

    Lemma mod_minus_one_eq : forall (n : nat), (n > 1) -> (-1) mod (Z.of_nat n) = ((Z.of_nat n)-1)%Z.
    Proof.
      intros.
      pose proof mod_minus_one n H.
      symmetry in H0.
      rewrite Zdiv.Zmod_small in H0.
      symmetry in H0.
      assumption.
      lia.
    Qed.

    Lemma mod_limit_wrap_eq : forall (a b m : Z), a = b mod m -> (0 <= a < m)%Z -> (0 <= b < m)%Z -> a = b.
    Proof.
      intros.
      rewrite Zdiv.Zmod_small in H.
      assumption.
      lia.
    Qed.

    
    Lemma mod_0_wrap_limit : forall (a : Z) (m : nat), 0%Z = a mod (Z.of_nat m) -> (-1 <= a < Z.of_nat m)%Z -> (m > 1) -> 0%Z = a.
    Proof.
      intros.
      assert ((0 <= a < Z.of_nat m)%Z \/ a = (-1)%Z).
      lia.
      destruct H2.
      rewrite Zdiv.Zmod_small in H.
      assumption.
      assumption.
      rewrite H2 in H.
      destruct m.
      lia.
      destruct m.
      lia.
      assert (-1 mod (Z.of_nat (S (S m))) = (Z.of_nat (S (m))))%Z.
      remember (S (S m)) as n.
      assert ((S m) = (n - 1)).
      lia.
      rewrite H3.
      assert ((Z.of_nat (n - 1) = (Z.of_nat n) - 1)%Z).
      lia.
      rewrite H4.
      apply mod_minus_one_eq.
      lia.
      rewrite H3 in H.
      discriminate.
    Qed.

    Lemma valid_implies_all_receives_causal_in_proj : forall (acts : list Action) (n : nat), acts_valid acts (S n) -> n > 1 -> all_receives_causal (project_to_size n acts) n.
    Proof.
      (*Unpack all the information we know*)
      intros.
      assert (Hn2 := H0).
      clear H0.
      unfold all_receives_causal in *.
      intros.
      unfold acts_valid in H.
      destruct H as [Hn H].
      destruct H.
      destruct H1.
      destruct H2.
      destruct H3.
      destruct H4.
      destruct H5 as [H5 Hpo].
      destruct Hpo as [Hpo Hrrc].
      destruct H0.
      (* Consider the cases for the receive *)
      destruct r.
      +
        (* It's actually a send *)
        contradiction.
      +
        (*It is a receive*)
        (*Unpack info based on the fact that it remains in the projection*)
        pose proof in_projection_remains acts (Receive dest m) n.
        destruct H7.
        pose proof H8 H6.
        clear H7 H8.
        destruct H9.
        (* Take a look at what it takes to be in the projection *)
        unfold in_projection in H8.
        simpl in H8.
        (* look case by case for n <= dest and determine that dest < n *)
        destruct Z_le_dec in H8; try contradiction.
        (* Unpack information we know based on the receive being causal in the system of size n+1 *)
        assert (isReceive (Receive dest m) /\ In (Receive dest m) acts).
        split; assumption.
        pose proof H2 (Receive dest m) H9.
        (* instatiate the action that is the send for this receive in the larger system *)
        inversion H10.
        destruct H11.
        destruct H12.
        (* Let's unpack what the old result looked like *)
        destruct x; try discriminate.
        (* Let's break this into the normal case and the wrap around case *)
        assert (((0 <= dest < Z.of_nat n)%Z) \/ ~((0 <= dest < Z.of_nat n)%Z)) as Hsmall1. lia.
        assert (((0 <= dest0 < Z.of_nat n)%Z) \/ ~((0 <= dest0 < Z.of_nat n)%Z)) as Hsmall2. lia.
        assert ((0 <= src < Z.of_nat n)%Z \/ ~(0 <= src < Z.of_nat n)%Z) as Hsmall3. lia.
        destruct Hsmall1, Hsmall2, Hsmall3.
        -- (*The normal case *)
          exists (Send src dest0 m0).
          assert (In (Send src dest0 m0) (project_to_size n acts)).
          rewrite <- in_projection_remains.
          split.
          assumption.
          unfold in_projection.
          simpl.
          destruct Z_le_dec.
          lia.
          destruct Z_lt_dec.
          lia.
          trivial.
          split.
          assumption.
          split.
          apply happens_before_independent_of_proj.
            split.
            assumption.
            split.
            assumption.
          apply in_projection_remains.
          split.
          assumption.
          (*Unpack that if it is in the projection then in_projection is true*)
          rewrite <- in_projection_remains in H6.
          destruct H6.
          assumption.
          (*Now the hard part. Lets first unpack what we know*)
          unfold is_send_for_receive in H13.
          destruct H13.
          (*Now lets see what we need *)
          unfold is_send_for_receive.
          split.
          (* lets solve the easy one first *)
          shelve.
          assumption.
          Unshelve.
          (* Unpack what node_eqb means *)
          unfold node_eq.
          unfold node_eq in H13.
          rewrite Zdiv.Zmod_small in H13.
          rewrite Zdiv.Zmod_small in H13.
          rewrite H13.
          reflexivity.
          lia.
          lia.
        -- (* only src wraps around *)

          (* The Send src is the only thing that wraps *)
           (* because of resitrictions on ids we know that src must be n *)
          assert (Hdest0 := H15).
          clear H15.
          assert (H15 := H16).
          clear H16.
          pose proof H4 (Send src dest0 m0) H11.
          assert (src = Z.of_nat n).
          simpl in *.
          lia.
          (* Because we know messages are always passed to direct neighbors we know dest0 too*)
          (* two possible cases for dest *)
          pose proof H4 (Receive dest m) H7.
          simpl in H18.
          assert (-1 <= dest < Z.of_nat n)%Z.
          lia.
          pose proof H5 (Send src dest0 m0) H11.
          simpl in H20.
          pose proof projected_in_or_out n (Send src dest0 m0).
          destruct H21.
          exists (Send src dest0 m0).
          split.
          apply in_projection_remains.
          split.
          assumption.
          unfold in_projection.
          rewrite H21.
          trivial.
          split.
          apply happens_before_independent_of_proj.
          split.
          assumption.
          split.
          apply in_projection_remains.
          split.
          assumption.
          unfold in_projection.
          rewrite H21.
          trivial.
          assumption.
          unfold is_send_for_receive.
          unfold is_send_for_receive in H13.
          destruct H13.
          split.
          unfold node_eq.
          unfold node_eq in H13.
          rewrite Zdiv.Zmod_small in H13.
          rewrite Zdiv.Zmod_small in H13.
          rewrite H13.
          reflexivity.
          lia.
          lia.
          assumption.
          rewrite H17 in H20.
          simpl in H16.
          destruct H16.
          unfold is_send_for_receive in H13.
          destruct H13.
          unfold node_eq in H13.
          destruct m0.
          assert (dest = 0%Z).
          lia.
          lia.
          destruct m.
          discriminate.
          assert (In (Send 0 (-1) Commit) (acts)).
          assert ((src <> 0%Z) /\ In (Send src dest0 Commit) acts).
          split.
          lia.
          assumption.
          pose proof H3 src dest0 Commit H24.
          destruct H25.
          assert (isReceive (Receive src Commit) /\ In (Receive src Commit) acts).
          split.
          trivial.
          assumption.
          pose proof H2 (Receive src Commit) H27.
          destruct H28.
          destruct H28.
          destruct H29.
          unfold is_send_for_receive in H30.
          destruct x; try contradiction.
          destruct H30.
          rewrite H31 in *.
          clear H31.
          unfold node_eq in H30.
          symmetry in H30.
          rewrite Zdiv.Zmod_small in H30.
          rewrite H17 in H30.
          pose proof H4 (Send src0 dest1 Commit) H28.
          simpl in H31.
          assert (dest1 = -1 \/ 0 <= dest1 <= Z.of_nat (S n))%Z.
          lia.
          destruct H32.
          pose proof H5 (Send src0 dest1 Commit) H28.
          simpl in H33.
          assert (src0 = 0)%Z.
          lia.
          rewrite H32 in H28.
          rewrite H34 in H28.
          assumption.
          pose proof H5 (Send src0 dest1 Commit) H28.
          simpl in H33.
          rewrite Zdiv.Zmod_small in H30.
          lia.
          lia.
          lia.
          assert (dest0 = ((Z.of_nat n) - 1)%Z).
          lia.
          rewrite H25 in H13.
          rewrite Zdiv.Zmod_small in H13.
          rewrite Zdiv.Zmod_small in H13.
          exists (Send 0 (-1) Commit).
          split.
          assert (has_required_actions (project_to_size n acts) n).
          apply has_required_actions_independent_of_proj.
          split.
          assumption.
          lia.
          unfold has_required_actions in H26.
          destruct H26.
          apply in_projection_remains.
          split.
          assumption.
          unfold in_projection.
          unfold projected.
          destruct Z_le_dec; try lia.
          destruct Z_lt_dec; try lia.
          split.
          pose proof Hpo (Send 0 (-1) Commit) (Receive dest Commit).
          simpl in H26.
          destruct H.
          apply happens_before_independent_of_proj.
          split.
          apply H26.
          unfold has_required_actions in H.
          assumption.
          assumption.
          split.
          apply in_projection_remains.
          split.
          assumption.
          unfold in_projection.
          simpl.
          destruct Z_le_dec.
          lia.
          destruct Z_lt_dec.
          lia.
          trivial.
          assumption.
          simpl.
          rewrite <- H13.
          unfold node_eq.
          simpl.
          assert (n > 1).
          lia.
          pose proof mod_minus_one n H26.
          split.
          lia.
          reflexivity.
          lia.
          lia.
        -- (* only dest0 wraps around *)
          pose proof H5 (Send src dest0 m0) H11.
          simpl in H17.
          exists (Send src dest0 m0).
          assert (In (Send src dest0 m0) (project_to_size n acts)).
          apply in_projection_remains.
          split.
          assumption.
          unfold in_projection.
          simpl.
          destruct Z_le_dec.
          lia.
          destruct Z_lt_dec.
          destruct m0.
          lia.
          lia.
          trivial.
          split.
          assumption.
          split.
          apply happens_before_independent_of_proj.
          split.
          assumption.
          split.
          assumption.
          assumption.
          unfold is_send_for_receive.
          unfold is_send_for_receive in H13.
          destruct H13.
          split.
          unfold node_eq in H13.
          destruct m0.
          rewrite Zdiv.Zmod_small in H13.
          assert (dest0 = dest).
          pose proof mod_limit_wrap_eq dest0 dest (Z.of_nat (S n)).
          apply H20.
          assumption.
          lia.
          lia.
          rewrite H20.
          unfold node_eq.
          reflexivity.
          lia.
          unfold node_eq.
          assert (dest0 = -1)%Z.
          lia.
          rewrite H20 in H13.
          rewrite mod_minus_one in H13.
          assert ((Z.of_nat (S n) - 1)%Z = Z.of_nat n).
          lia.
          rewrite H21 in H13.
          rewrite Zdiv.Zmod_small in H13.
          assert (Z.of_nat n = dest).
          pose proof mod_limit_wrap_eq (Z.of_nat n) dest (Z.of_nat (S n)).
          apply H22.
          assumption.
          lia.
          lia.
          lia.
          lia.
          lia.
          assumption.
        --
          (* both src and dest0 wrap but not dest *)
          unfold is_send_for_receive in H13.
          destruct H13.
          unfold node_eq in H13.
          symmetry in H13.
          rewrite Zdiv.Zmod_small in H13.
          pose proof H4 (Send src dest0 m0) H11.
          simpl in H18.
          assert (dest0 = (-1)%Z \/ (dest0 >= (Z.of_nat (n)))%Z).
          lia.
          destruct H19.
          rewrite H19 in H13.
          rewrite mod_minus_one_eq in H13.
          lia.
          lia.
          assert ((dest0 = (Z.of_nat (n))) \/ (dest0 = (Z.of_nat (S n)))).
          lia.
          destruct H20.
          rewrite Zdiv.Zmod_small in H13.
          lia.
          lia.
          rewrite H20 in H13.
          rewrite Zdiv.Z_mod_same in H13.
          destruct m.
          exists (Send (Z.of_nat (n - 1)) (Z.of_nat (n)) Promise).
          assert (In (Send (Z.of_nat (n - 1)) (Z.of_nat n) Promise) (project_to_size n acts)).
          unfold has_required_actions in H.
          destruct H.
          assert ((S (n - 1)) < (S n)).
          lia.
          pose proof H21 (n - 1) H22.
          destruct H23.
          apply in_projection_remains.
          split.
          assert ((S (n - 1)) = n).
          lia.
          rewrite H25 in H23.
          assumption.
          unfold in_projection.
          simpl.
          destruct Z_le_dec.
          lia.
          destruct Z_lt_dec.
          lia.
          trivial.
          split.
          assumption.
          split.
          unfold phase_sequence_correct in Hpo.
          rewrite H13 in H7.
          pose proof in_proj_in_orig acts (Send (Z.of_nat (n - 1)) (Z.of_nat n) Promise) n H21.
          pose proof Hpo (Receive 0 Promise) (Send (Z.of_nat (n - 1)) (Z.of_nat n) Promise) H7 H22.
          simpl in H23.
          rewrite H13.
          apply happens_before_independent_of_proj.
          split.
          assumption.
          split.
          assumption.
          rewrite <- H13.
          assumption.
          unfold is_send_for_receive.
          unfold node_eq.
          rewrite Zdiv.Z_mod_same.
          rewrite H13.
          rewrite Zdiv.Zmod_0_l.
          split.
          reflexivity.
          reflexivity.
          lia.
          exists (Send (1)%Z (0)%Z Commit).
          assert (In (Send 1 0 Commit) (project_to_size n acts)).
          unfold has_required_actions in H.
          destruct H.
          destruct H.
          ++
          assert (1 < S n).
          lia.
          assert (0 >= x \/ 0 < x).
          lia.
          destruct H23.
          pose proof H (0).
          destruct H24.
          pose proof H24 H23 H22.
          apply in_projection_remains.
          split.
          destruct H26.
          assumption.
          unfold in_projection.
          simpl.
          destruct Z_le_dec.
          lia.
          destruct Z_lt_dec.
          lia.
          trivial.
          inversion H10.
          assert (x0 = (Send 1 0 Commit)).
          destruct H24.
          destruct H25.
          unfold is_send_for_receive in H26.
          destruct x0; try discriminate.
          destruct H26.
          destruct m; try discriminate.
          rewrite H13 in H26.
          unfold node_eq in H26.
          rewrite Zdiv.Zmod_0_l in H26.
          replace (dest1 mod Z.of_nat (S n)) with dest1 in H26.
          pose proof H5 (Send src0 dest1 Commit) H24.
          simpl in H28.
          rewrite H26.
          rewrite H26 in H28.
          simpl in H28.
          rewrite <- H28.
          reflexivity.
          pose proof H4 (Send src0 dest1 Commit) H24. 
          simpl in H28.
          simpl.
          pose proof H5 (Send src0 dest1 Commit) H24.
          simpl in H29.
          symmetry in H26.
          assert (H26c := H26).
          apply mod_0_wrap_limit in H26.
          rewrite H26 in H26c.
          simpl in H26c.
          assumption.
          lia.
          lia.
          contradiction.
          contradiction.
          contradiction.
          rewrite H25 in H24.
          destruct H24.
          apply in_projection_remains.
          split.
          assumption.
          unfold in_projection.
          simpl.
          destruct Z_le_dec.
          lia.
          destruct Z_lt_dec.
          lia.
          trivial.
          ++
          split.
          assumption.
          split.
          unfold phase_sequence_correct in Hpo.
          rewrite H13 in H7.
          pose proof in_proj_in_orig acts (Send 1 0 Commit) n H21.
          pose proof Hpo (Receive 0 Commit) (Send (1)%Z 0%Z Commit) H7 H22.
          simpl in H23.
          rewrite H13.
          apply happens_before_independent_of_proj.
          split.
          assumption.
          split.
          assumption.
          rewrite <- H13.
          assumption.
          unfold is_send_for_receive.
          unfold node_eq.
          rewrite H13.
          rewrite Zdiv.Zmod_0_l.
          split.
          reflexivity.
          reflexivity.
          ++
          lia.
          ++
          lia.
        -- (* only dest wraps *)
          (* Show that dest id must be out of range *)
          pose proof H4 (Receive dest m) H7.
          simpl in H17.
          lia.
        -- (* dest and src wrap but dest0 doesn't *)
          (* Show that dest0 equals must equal n which is a contradiction *)
          pose proof H4 (Receive dest m) H7.
          simpl in H17.
          lia.
        -- (* both dests wrap but src dosen't *)
          (* Show that dest0 equals must equal n which is a contradiction *)
          pose proof H4 (Receive dest m) H7.
          simpl in H17.
          lia.
        -- (* all three wrap *)
          (* Show that dest0 equals must equal n which is a contradiction *)
          pose proof H4 (Receive dest m) H7.
          simpl in H17.
          lia.
        --
         contradiction.
        --
         contradiction.
        --
         contradiction.
      + (*Is a sendRef*)
          simpl in H0.
          contradiction.
      + (*Is a receiveRef*)
          simpl in H0.
          contradiction.
    Qed.

  Lemma all_sends_triggered_independent_of_proj : forall (acts : list Action) (n : nat), all_sends_triggered acts -> all_sends_triggered (project_to_size n acts).
  Proof.
    intros.
    unfold all_sends_triggered in *.
    intros.
    pose proof (H src dest m).
    assert (
     In (Receive src m) acts /\
     happens_before (Receive src m) (Send src dest m) acts
    ).
    apply H1.
    split.
    destruct H0.
    assumption.
    destruct H0.
    apply in_proj_in_orig with (size := n).
    assumption.
    destruct H1.
    destruct H0.
    split.
    assumption.
    apply in_proj_in_orig with (size := n).
    assumption.
    split.
    apply in_projection_remains.
    split.
    assumption.
      destruct H0.
      rewrite <- in_projection_remains in H4.
      destruct H4.
      unfold in_projection in H5.
      simpl in H5.
      destruct (Z_le_dec (Z.of_nat n) src); try contradiction.
      unfold in_projection.
      simpl.
      destruct Z_le_dec; try contradiction.
      trivial.
    apply happens_before_independent_of_proj.
    split.
    assumption.
    split.
      destruct H0.
      rewrite <- in_projection_remains in H4.
      destruct H4.
      unfold in_projection in H5.
      simpl in H5.
      destruct Z_le_dec; try contradiction.
      apply in_projection_remains.
      split.
      assumption.
      unfold in_projection.
      simpl.
      destruct Z_le_dec; try contradiction.
      trivial.
    destruct H0.
    assumption.
  Qed.

  Ltac apply_happens_before_iop := apply happens_before_independent_of_proj; split; try assumption; split; try assumption.

  Lemma phase_sequence_correct_independent_of_proj : forall (acts : list Action) (n : nat), phase_sequence_correct acts -> phase_sequence_correct (project_to_size n acts).
  Proof.
    intros.
    unfold phase_sequence_correct.
    intros.
    pose proof in_proj_in_orig acts a n H0.
    pose proof in_proj_in_orig acts b n H1.
    pose proof H a b H2 H3.
    destruct a, b.
    destruct src, dest, m; try trivial.
    destruct p; try trivial.
    destruct src0, dest0, m0; try trivial; try apply_happens_before_iop.
    destruct p; try trivial; try apply_happens_before_iop.
    destruct src; try trivial; try apply_happens_before_iop;
    destruct dest; try trivial; try apply_happens_before_iop.
    destruct p; try trivial; try apply_happens_before_iop.
    destruct m; try trivial; try apply_happens_before_iop.
    destruct m0; try trivial; try apply_happens_before_iop.
    destruct dest; try trivial; try apply_happens_before_iop.
    destruct dest; try trivial; try apply_happens_before_iop.
    destruct dest; try trivial; try apply_happens_before_iop.
    destruct dest; try trivial; try apply_happens_before_iop.
    destruct dest; try trivial; try apply_happens_before_iop.
    destruct dest; try trivial; try apply_happens_before_iop.
    destruct m; try trivial; try apply_happens_before_iop.
    destruct m; try trivial; try apply_happens_before_iop.
    trivial.
    trivial.
    trivial.
    trivial.
    trivial.
    trivial.
  Qed.

  Lemma all_ref_recieves_causal_independent_of_proj : forall (acts : list Action) (n : nat), all_ref_receives_causal acts (S n) -> all_ref_receives_causal (project_to_size n acts) n.
  Proof.
    intros.
    unfold all_ref_receives_causal in *.
    intros.
    assert (isReceiveRef r /\ In r acts).
    split.
    destruct H0.
    assumption.
    apply in_proj_in_orig with (size := n).
    destruct H0.
    assumption.
    pose proof H r H1.
    inversion H2.
    exists x.
    assert (in_projection n x \/ ~in_projection n x).
    unfold in_projection.
    destruct (projected n x).
    left; trivial.
    right; red; trivial.
    destruct H4.
    split.
    apply in_projection_remains.
    split.
    destruct H3.
    assumption.
    assumption.
    destruct H3.
    destruct H5.
    split.
    apply happens_before_independent_of_proj.
    split.
    assumption.
    split.
    apply in_projection_remains.
    split.
    assumption.
    assumption.
    destruct H0.
    assumption.
    assumption.
    (*Show that if x is not in the projection then r is not in the projection*)
    destruct H3.
    destruct H5.
    unfold is_sendRef_for_receiveRef in H6.
    destruct x; try contradiction.
    destruct r; try contradiction.
    destruct H0.
    apply in_projection_remains in H7.
    destruct H7.
    unfold in_projection in *.
    unfold projected in *.
    destruct Z_le_dec; try contradiction.
    destruct Z_le_dec.
    lia.
    contradiction.
  Qed.
      

  Lemma larger_conforms_to_smaller : forall (acts : list Action) (n : nat), acts_valid acts (S n)  /\ n > 1 -> acts_valid (project_to_size n acts) n.
    Proof.
      intros.
      destruct H.
      assert (Hd := H).
      unfold acts_valid in H.
      unfold acts_valid.
      destruct H.
      destruct H1.
      destruct H2.
      destruct H3.
      destruct H4.
      destruct H5.
      destruct H6.
      destruct H7.
      split.
      lia.
      split.
      apply has_required_actions_independent_of_proj.
      split; try assumption; try lia.
      split.
      (*apply has_no_duplicate_receives_independent_of_proj.*)
      apply has_no_duplicate_receives_independent_of_proj.
      assumption.
      split.
      apply valid_implies_all_receives_causal_in_proj.
      assumption.
      lia.
      split.
      apply all_sends_triggered_independent_of_proj.
      assumption.
      split.
      apply all_ids_in_range_independent_of_proj.
      assumption.
      split.
      apply promise_forward_commit_backward_independent_of_proj.
      assumption.
      split.
      apply phase_sequence_correct_independent_of_proj.
      assumption.
      apply all_ref_recieves_causal_independent_of_proj.
      assumption.
    Qed.

    Lemma project_idempotent : forall (acts : list Action) (n0 n1 : nat), n0 < n1 -> (project_to_size n0 (project_to_size n1 acts)) = (project_to_size n0 acts).
    Proof.
      intros.
      induction acts.
      simpl.
      reflexivity.
      simpl.
      destruct a.
      -
      unfold projected.
      destruct Z_le_dec.
      destruct Z_le_dec.
      apply IHacts.
      lia.
      simpl.
      destruct Z_le_dec.
      destruct Z_lt_dec.
      apply IHacts.
      simpl.
      destruct Z_le_dec.
      apply IHacts.
      destruct Z_lt_dec.
      apply IHacts.
      lia.
      destruct Z_lt_dec.
      destruct Z_lt_dec.
      apply IHacts.
      lia.
      destruct Z_lt_dec.
      simpl.
      destruct Z_le_dec.
      apply IHacts.
      destruct Z_lt_dec.
      apply IHacts.
      lia.
      simpl.
      destruct Z_le_dec.
      lia.
      destruct Z_lt_dec.
      lia.
      f_equal.
      apply IHacts.
      -
      unfold projected.
      destruct Z_le_dec.
      destruct Z_le_dec.
      apply IHacts.
      lia.
      simpl.
      destruct Z_le_dec.
      apply IHacts.
      f_equal.
      apply IHacts.
      -
      unfold projected.
      destruct Z_le_dec.
      destruct Z_le_dec.
      apply IHacts.
      lia.
      simpl.
      destruct Z_le_dec.
      apply IHacts.
      f_equal.
      apply IHacts.
      -
      unfold projected.
      destruct Z_le_dec.
      destruct Z_le_dec.
      apply IHacts.
      lia.
      simpl.
      destruct Z_le_dec.
      apply IHacts.
      f_equal.
      apply IHacts.
    Qed.

  Lemma projected_larger_conforms_to_smaller : forall (acts : list Action) (n : nat), acts_valid (project_to_size (S n) acts) (S n) /\ n > 1 -> acts_valid (project_to_size n acts) n.
    Proof.
      intros.
      destruct H.
      assert (Hd := H).
      unfold acts_valid in H.
      unfold acts_valid.
      destruct H.
      destruct H1.
      destruct H2.
      destruct H3.
      destruct H4.
      split.
      assumption.
      pose proof (has_required_actions_independent_of_proj (project_to_size (S n) acts) n).
      rewrite project_idempotent in H6.
      split.
      apply H6.
      split.
      assumption.
      lia.
      split.
      pose proof (has_no_duplicate_receives_independent_of_proj (project_to_size (S n) acts) n).
      (*pose proof (has_no_duplicate_actions_independent_of_proj (project_to_size (S n) acts) n).*)
      rewrite project_idempotent in H7.
      apply H7.
      assumption.
      lia.
      split.
      pose proof (valid_implies_all_receives_causal_in_proj (project_to_size (S n) acts) n).
      rewrite project_idempotent in H7.
      apply H7.
      assumption.
      lia.
      lia.
      pose proof (all_sends_triggered_independent_of_proj (project_to_size (S n) acts) n).
      rewrite project_idempotent in H7.
      split.
      apply H7.
      assumption.
      pose proof (all_ids_in_range_independent_of_proj (project_to_size (S n) acts) n).
      rewrite project_idempotent in H8.
      split.
      apply H8.
      destruct H5.
      assumption.
      split.
      pose proof (promise_forward_commit_backward_independent_of_proj (project_to_size (S n) acts) n).
      rewrite project_idempotent in H9.
      apply H9.
      destruct H5.
      destruct H10.
      assumption.
      lia.
      pose proof (phase_sequence_correct_independent_of_proj (project_to_size (S n) acts) n).
      rewrite project_idempotent in H9.
      split.
      apply H9.
      destruct H5.
      destruct H10.
      destruct H11.
      assumption.
      pose proof (all_ref_recieves_causal_independent_of_proj (project_to_size (S n) acts) n).
      rewrite project_idempotent in H10.
      apply H10.
      destruct H5.
      destruct H11.
      destruct H12.
      assumption.
      lia.
      lia.
      lia.
      lia.
      lia.
    Qed.

    Theorem all_valid_systems_conform_to_size_3 : forall (acts : list Action) (n : nat), acts_valid acts n /\ n > 3 -> acts_valid (project_to_size 3 acts) 3.
    Proof.
      intros.
      destruct H.
      destruct n.
      lia.
      destruct n.
      lia.
      destruct n.
      lia.
      destruct n.
      lia.
      destruct n.
      apply larger_conforms_to_smaller.
      split.
      assumption.
      lia.
      assert (acts_valid (project_to_size (S (S (S (S n)))) acts) (S (S (S (S n))))).
      apply larger_conforms_to_smaller.
      split.
      assumption.
      lia.
      clear H.
      clear H0.
      induction n.
      apply projected_larger_conforms_to_smaller.
      split.
      assumption.
      lia.
      apply IHn.
      apply projected_larger_conforms_to_smaller.
      split.
      assumption.
      lia.
    Qed.

End Conformance.
