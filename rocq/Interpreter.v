From Stdlib Require Import List NArith.
From Loosevm Require Import Syntax State Semantics.
Definition step code s : option state :=
  match mode s with
  | Running => Some (match decode code (pc s) with
                     | Some i => execute code s i
                     | None => finish s (Fault Decode) end)
  | _ => None end.
Theorem step_correspondence code s t : step code s = Some t <-> transition code s t.
Proof.
  split.
  - unfold step. destruct (mode s) eqn:M; try discriminate.
    destruct (decode code (pc s)) eqn:D; intro H; inversion H; subst.
    + eapply decoded; eauto.
    + now apply malformed.
  - intro H. inversion H; subst; unfold step; rewrite H0, H1; reflexivity.
Qed.
Theorem stopped_has_no_step code s : mode s <> Running -> step code s = None.
Proof. unfold step. destruct (mode s); congruence. Qed.
Theorem running_progress code s : mode s = Running -> exists t, transition code s t.
Proof.
  intro H. destruct (decode code (pc s)) eqn:D.
  - eexists. eapply decoded; eauto.
  - eexists. now apply malformed.
Qed.
Fixpoint run fuel code s :=
  match fuel with
  | O => s
  | S n => match step code s with Some t => run n code t | None => s end
  end.
Inductive steps code : state -> state -> Prop :=
| steps_refl s : steps code s s
| steps_cons s t u : transition code s t -> steps code t u -> steps code s u.
Lemma steps_trans code s t u : steps code s t -> steps code t u -> steps code s u.
Proof. intros H. induction H; eauto using steps. Qed.
Lemma run_steps fuel code s : steps code s (run fuel code s).
Proof.
  revert s. induction fuel; intro s; cbn; try constructor.
  destruct (step code s) eqn:H.
  - eapply steps_cons; [apply step_correspondence; exact H | apply IHfuel].
  - constructor.
Qed.
