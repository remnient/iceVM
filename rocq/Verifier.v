From Stdlib Require Import List NArith Arith Bool Lia.
From IceVM Require Import Syntax State Semantics Interpreter.
Import ListNotations.
Local Opaque memory_size stack_size.
Fixpoint covers fuel code p :=
  if Nat.eqb p (length code) then true else
  match fuel with
  | 0 => false
  | S fuel => match decode code p with
              | Some i => covers fuel code (p + width i) | None => false end
  end.
Definition check_at code p :=
  match decode code p with
  | None => false
  | Some i =>
      let next := local_target code p (p + width i) in
      match i with
      | Halt => Nat.eqb (owner code p) 0
      | Ret => negb (Nat.eqb (owner code p) 0)
      | Trap | Indirect _ => true
      | Jump t => local_target code p t
      | Branch _ t => local_target code p t && next
      | Call t => call_target code t && next
      | _ => next end
  end.
Definition verify code :=
  match decode code 0 with
  | Some Entry => covers (length code) code 0 && forallb (check_at code) (boundaries code)
  | _ => false end.
Definition structural code s :=
  boundary code (pc s) = true /\
  Forall (fun f => boundary code (return_pc f) = true) (frames s).
Lemma checked_boundary code p : verify code = true -> boundary code p = true -> check_at code p = true.
Proof.
  unfold verify, boundary. destruct (decode code 0) as [i|]; try discriminate.
  destruct i; try discriminate. rewrite andb_true_iff. intros [_ H] B.
  apply forallb_forall with (x := p) in H; auto.
  apply existsb_exists in B. destruct B as [x [Hin Hx]].
  apply Nat.eqb_eq in Hx. now subst.
Qed.
Lemma local_boundary code p t : local_target code p t = true -> boundary code t = true.
Proof. unfold local_target. rewrite !andb_true_iff. tauto. Qed.
Lemma call_boundary code t : call_target code t = true -> boundary code t = true.
Proof. unfold call_target. rewrite andb_true_iff. tauto. Qed.
Lemma checked_decode code p : check_at code p = true -> exists i, decode code p = Some i.
Proof. unfold check_at. destruct (decode code p); eauto; discriminate. Qed.
Lemma execute_structural code s i :
  structural code s -> decode code (pc s) = Some i -> check_at code (pc s) = true ->
  structural code (execute code s i).
Proof.
  intros [Hp Hfs] D H. unfold check_at in H. rewrite D in H.
  destruct i; cbn [execute] in *;
  unfold transfer, write_reg, at_pc, finish; cbn;
  repeat match goal with
  | H : (_ && _) = true |- _ => apply andb_true_iff in H; destruct H
  end;
  repeat match goal with
  | |- context [if ?b then _ else _] => destruct b eqn:?
  | |- context [match ?x with Some _ => _ | None => _ end] => destruct x eqn:?
  | |- context [match frames s with _ => _ end] => destruct (frames s) eqn:?
  end;
  unfold structural; cbn;
  try (split; [assumption | assumption]);
  try (split; [eauto using local_boundary, call_boundary | assumption]);
  try (split; [eauto using local_boundary, call_boundary | constructor; eauto using local_boundary]);
  inversion Hfs; subst; auto.
Qed.
Theorem verifier_sound code s t :
  verify code = true -> structural code s -> transition code s t -> structural code t.
Proof.
  intros V S T. inversion T; subst.
  - eapply execute_structural.
    + exact S.
    + eassumption.
    + apply checked_boundary; [exact V | exact (proj1 S)].
  - exact S.
Qed.
Theorem accepted_no_decode_fault code s :
  verify code = true -> structural code s ->
  exists i, decode code (pc s) = Some i.
Proof. intros V [B _]. apply checked_decode. eauto using checked_boundary. Qed.
Lemma accepted_initial code : verify code = true -> structural code initial.
Proof.
  unfold verify. destruct (decode code 0) as [i|] eqn:D; try discriminate.
  destruct i; try discriminate. intro V. split; [|constructor].
  unfold boundary, boundaries. destruct code; try discriminate.
  cbn [length scan]. rewrite D. cbn. reflexivity.
Qed.
Theorem verified_execution code t : verify code = true -> steps code initial t -> structural code t.
Proof.
  intros V H. assert (S : structural code initial) by now apply accepted_initial.
  revert S. induction H; auto. intro S. apply IHsteps. eauto using verifier_sound.
Qed.
Inductive disciplined code : nat -> list frame -> Prop :=
| root_frame p : owner code p = 0 -> disciplined code p []
| nested_frame p f fs : owner code p <> 0 -> disciplined code (return_pc f) fs ->
    disciplined code p (f :: fs).
Lemma disciplined_local code p t fs :
  local_target code p t = true -> disciplined code p fs -> disciplined code t fs.
Proof.
  unfold local_target. rewrite andb_true_iff. intros [_ E] S.
  apply Nat.eqb_eq in E. inversion S; subst; constructor; congruence.
Qed.
Lemma callable_nonroot code t : call_target code t = true -> owner code t <> 0.
Proof.
  unfold call_target. rewrite andb_true_iff. intros [_ H].
  destruct (decode code t) as [i|]; try discriminate.
  destruct i; try discriminate. apply andb_true_iff in H.
  destruct H as [_ H]. apply Bool.negb_true_iff in H. now apply Nat.eqb_neq.
Qed.
Lemma execute_disciplined code s i :
  disciplined code (pc s) (frames s) ->
  decode code (pc s) = Some i -> check_at code (pc s) = true ->
  disciplined code (pc (execute code s i)) (frames (execute code s i)).
Proof.
  intros S D H. unfold check_at in H. rewrite D in H.
  destruct i; cbn [execute] in *;
  unfold transfer, write_reg, at_pc, finish; cbn;
  repeat match goal with
  | H : (_ && _) = true |- _ => apply andb_true_iff in H; destruct H
  end;
  repeat match goal with
  | |- context [if ?b then _ else _] => destruct b eqn:?
  | |- context [match ?x with Some _ => _ | None => _ end] => destruct x eqn:?
  | |- context [match frames s with _ => _ end] => destruct (frames s) eqn:?
  end; cbn; try exact S; try solve [eapply disciplined_local; [eassumption | exact S]];
  try solve [inversion S; subst; assumption].
  apply andb_true_iff in Heqb. destruct Heqb as [C L].
  constructor; [now apply callable_nonroot | eapply disciplined_local; eauto].
Qed.
Theorem verifier_stack_discipline code s t :
  verify code = true -> structural code s -> disciplined code (pc s) (frames s) ->
  transition code s t -> disciplined code (pc t) (frames t).
Proof.
  intros V B S T. inversion T; subst; auto.
  eapply execute_disciplined; eauto. apply checked_boundary; [exact V | exact (proj1 B)].
Qed.
Theorem accepted_return_has_caller code s :
  verify code = true -> structural code s -> disciplined code (pc s) (frames s) ->
  decode code (pc s) = Some Ret -> frames s <> [].
Proof.
  intros V B S D F. pose proof (checked_boundary code (pc s) V (proj1 B)) as H.
  unfold check_at in H. rewrite D in H. cbn in H.
  rewrite F in S. inversion S; subst. rewrite H0 in H. discriminate.
Qed.
Lemma owner_zero code : owner code 0 = 0.
Proof.
  unfold owner. destruct code; cbn [length owner_at]; auto.
  destruct (decode (n :: code) 0) as [i|]; auto. now destruct i.
Qed.
Theorem verified_invariants code s : verify code = true -> steps code initial s ->
  structural code s /\ disciplined code (pc s) (frames s) /\ well_formed s /\ canonical s.
Proof.
  intros V E.
  assert (I : structural code initial /\ disciplined code (pc initial) (frames initial) /\
              well_formed initial /\ canonical initial).
  { split; [now apply accepted_initial |].
    split; [constructor; apply owner_zero |].
    split; [apply initial_well_formed | apply initial_canonical]. }
  revert I. induction E; auto. intros [B [D [W C]]].
  apply IHE. split; [eapply verifier_sound; eauto |].
  split; [eapply verifier_stack_discipline; eauto |].
  split; [eapply transition_well_formed; eauto | eapply transition_canonical; eauto].
Qed.
Theorem verified_return_runs code s :
  verify code = true -> steps code initial s -> decode code (pc s) = Some Ret ->
  mode (execute code s Ret) = Running.
Proof.
  intros V E R. destruct (verified_invariants code s V E) as [B [D _]].
  pose proof (accepted_return_has_caller code s V B D R) as C.
  destruct B as [_ F]. destruct (frames s) as [|f fs] eqn:Fs; try contradiction.
  inversion F; subst. cbn [execute]. rewrite Fs. rewrite H1. reflexivity.
Qed.
