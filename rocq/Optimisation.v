From Stdlib Require Import List NArith Arith Bool Lia.
From IceVM Require Import Syntax State Semantics Interpreter Verifier Compiler Simulation.
Import ListNotations.
Definition equivalent_state s t :=
  pc s = pc t /\ mode s = mode t /\
  (forall r, regs s r = regs t r) /\
  mem s = mem t /\ frontier s = frontier t /\ frames s = frames t.
Lemma put_shadow r d x y n : put (put r d x) d y n = put r d y n.
Proof. unfold put. now destruct (Nat.eqb n d). Qed.
Theorem dead_store code s d x y : mode s = Running ->
  equivalent_state
    (execute_sequence code s [Imm d x; Imm d y])
    (execute_sequence code s [Pad 8; Imm d y]).
Proof.
  intro M. cbn [execute_sequence]. rewrite M.
  cbn [execute write_reg at_pc mode pc regs mem frontier frames].
  unfold equivalent_state. cbn. repeat split; auto; try lia.
  intro r. apply put_shadow.
Qed.
Theorem redundant_move code s d : mode s = Running -> word (regs s d) = regs s d ->
  equivalent_state (execute_sequence code s [Move d d]) (execute_sequence code s [Pad 1]).
Proof.
  intros M W. cbn [execute_sequence]. rewrite M.
  cbn [execute write_reg at_pc mode pc regs mem frontier frames].
  unfold equivalent_state. cbn. repeat split; auto.
  intro r. unfold put. destruct (Nat.eqb r d) eqn:E; auto.
  apply Nat.eqb_eq in E. now subst.
Qed.
Theorem constant_propagation code s d x op v :
  mode s = Running -> eval_bin op (word x) (word x) = Some v ->
  equivalent_state
    (execute_sequence code s [Imm d x; Binary op d d d])
    (execute_sequence code s [Imm d v; Pad 2]).
Proof.
  intros M E. cbn [execute_sequence]. rewrite M.
  cbn [execute write_reg at_pc mode pc regs mem frontier frames].
  rewrite !put_same, E. unfold equivalent_state.
  cbn [write_reg at_pc mode pc regs mem frontier frames].
  repeat split; auto; try lia. intro r. apply put_shadow.
Qed.
Theorem branch_false code s a x target :
  mode s = Running -> word x = 0%N ->
  execute_sequence code s [Imm a x; Branch a target] =
  execute_sequence code s [Imm a x; Pad 8].
Proof.
  intros M X. cbn [execute_sequence]. rewrite M.
  cbn [execute write_reg at_pc mode pc regs mem frontier frames].
  rewrite put_same, X. reflexivity.
Qed.
Theorem branch_true code s a x target :
  mode s = Running -> word x <> 0%N ->
  execute_sequence code s [Imm a x; Branch a target] =
  execute_sequence code s [Imm a x; Jump target].
Proof.
  intros M X. cbn [execute_sequence]. rewrite M.
  cbn [execute write_reg at_pc mode pc regs mem frontier frames].
  rewrite put_same. apply N.eqb_neq in X. now rewrite X.
Qed.

Definition registers_equal (a b : registers) := forall n, a n = b n.
Definition frame_equal a b := return_pc a = return_pc b /\ registers_equal (saved a) (saved b).
Definition states_equal a b :=
  pc a = pc b /\ mode a = mode b /\ mem a = mem b /\ frontier a = frontier b /\
  registers_equal (regs a) (regs b) /\ Forall2 frame_equal (frames a) (frames b).
Lemma registers_equal_refl r : registers_equal r r.
Proof. intro n. reflexivity. Qed.
Lemma registers_equal_sym r q : registers_equal r q -> registers_equal q r.
Proof. intros E n. symmetry. apply E. Qed.
Lemma registers_equal_trans r q t : registers_equal r q -> registers_equal q t -> registers_equal r t.
Proof. intros E F n. now rewrite E, F. Qed.
Lemma frames_equal_refl fs : Forall2 frame_equal fs fs.
Proof. induction fs; constructor; auto. split; [reflexivity | apply registers_equal_refl]. Qed.
Lemma frames_equal_sym fs gs : Forall2 frame_equal fs gs -> Forall2 frame_equal gs fs.
Proof.
  intro H. induction H; constructor; auto. destruct H as [P R].
  split; auto using registers_equal_sym.
Qed.
Lemma frames_equal_trans fs gs hs :
  Forall2 frame_equal fs gs -> Forall2 frame_equal gs hs -> Forall2 frame_equal fs hs.
Proof.
  intros F. revert hs. induction F; intros hs G.
  - inversion G. constructor.
  - inversion G as [|y' z ys' zs Rel Tail]; subst. constructor; auto.
    destruct H as [P R]. destruct Rel as [P' R']. split; eauto using registers_equal_trans; congruence.
Qed.
Lemma states_equal_refl s : states_equal s s.
Proof. repeat split; auto using registers_equal_refl, frames_equal_refl. Qed.
Lemma states_equal_sym s t : states_equal s t -> states_equal t s.
Proof.
  intros [P [M [H [F [R S]]]]]. repeat split; auto using registers_equal_sym, frames_equal_sym.
Qed.
Lemma states_equal_trans s t u : states_equal s t -> states_equal t u -> states_equal s u.
Proof.
  intros [P [M [H [F [R S]]]]] [P' [M' [H' [F' [R' S']]]]].
  repeat split; eauto using registers_equal_trans, frames_equal_trans; congruence.
Qed.
Lemma put_equal r q d v : registers_equal r q -> registers_equal (put r d v) (put q d v).
Proof. intros E n. unfold put. destruct (Nat.eqb n d); auto. Qed.
Lemma equivalent_states s t : equivalent_state s t -> states_equal s t.
Proof.
  intros [P [M [R [H [F S]]]]]. repeat split; auto.
  rewrite S. apply frames_equal_refl.
Qed.
Definition same_guards c d p :=
  (forall t, local_target c p t = local_target d p t) /\
  (forall t, call_target c t = call_target d t) /\
  (forall t, boundary c t = boundary d t).
Local Opaque memory_size stack_size.
Lemma execute_equal c d s t i : states_equal s t -> same_guards c d (pc s) ->
  states_equal (execute c s i) (execute d t i).
Proof.
  intros [P [M [H [F [R S]]]]] [L [C B]].
  assert (Len : length (frames s) = length (frames t)) by now apply Forall2_length in S.
  destruct i; cbn [execute]; unfold transfer, at_pc, write_reg, finish; cbn;
  repeat rewrite <- P; repeat rewrite <- H; repeat rewrite <- F;
  repeat rewrite <- R; repeat rewrite <- Len;
  repeat rewrite <- L; repeat rewrite <- C; repeat rewrite <- B;
  repeat match goal with
  | |- context [if ?b then _ else _] => destruct b eqn:?
  | |- context [match ?x with Some _ => _ | None => _ end] => destruct x eqn:?
  end;
  try solve [unfold states_equal; cbn; repeat split; auto using put_equal;
             try (constructor; [split; cbn; auto | assumption])].
  destruct S as [|f g fs gs FG FGS]; cbn.
  - unfold states_equal; cbn. repeat split; auto.
  - destruct FG as [RP SR]. rewrite RP, <- B.
    destruct (boundary c (return_pc g)); unfold states_equal; cbn;
      repeat split; auto using put_equal.
    constructor; auto. split; auto.
Qed.
Lemma boundary_member c p : boundary c p = true <-> In p (boundaries c).
Proof.
  unfold boundary. rewrite existsb_exists. split.
  - intros [q [I E]]. apply Nat.eqb_eq in E. now subst.
  - intro I. exists p. split; auto. apply Nat.eqb_refl.
Qed.
Definition metadata_check c d :=
  if list_eq_dec Nat.eq_dec (boundaries c) (boundaries d) then
    forallb (fun p => Nat.eqb (owner c p) (owner d p) && Bool.eqb (call_target c p) (call_target d p)) (boundaries c)
  else false.
Lemma metadata_boundaries c d : metadata_check c d = true -> forall p, boundary c p = boundary d p.
Proof.
  unfold metadata_check. destruct (list_eq_dec Nat.eq_dec (boundaries c) (boundaries d)); try discriminate.
  intros _ p. unfold boundary. now rewrite e.
Qed.
Lemma metadata_entry c d p : metadata_check c d = true -> boundary c p = true ->
  owner c p = owner d p /\ call_target c p = call_target d p.
Proof.
  unfold metadata_check. destruct (list_eq_dec Nat.eq_dec (boundaries c) (boundaries d)); try discriminate.
  intros H P. apply boundary_member in P. rewrite forallb_forall in H. specialize (H p P).
  apply andb_true_iff in H. destruct H as [O C].
  apply Nat.eqb_eq in O. apply Bool.eqb_prop in C. auto.
Qed.
Lemma metadata_guards c d p : metadata_check c d = true -> boundary c p = true -> same_guards c d p.
Proof.
  intros H P. pose proof (metadata_boundaries c d H) as B.
  pose proof (proj1 (metadata_entry c d p H P)) as O.
  split.
  - intro t. unfold local_target. rewrite <- (B p), <- (B t), P. destruct (boundary c t) eqn:T; cbn; auto.
    pose proof (proj1 (metadata_entry c d t H T)) as O'. now rewrite O, O'.
  - split; [|exact B]. intro t. destruct (boundary c t) eqn:T.
    + exact (proj2 (metadata_entry c d t H T)).
    + unfold call_target. rewrite <- B, T. reflexivity.
Qed.
Inductive rewrite_rule :=
| Keep (i : instr)
| RemoveMove (d : nat)
| Overwrite (d : nat) (x y : N)
| Fold (d : nat) (x : N) (op : binop) (v : N)
| RemoveBranch (a : nat) (x : N) (target : nat).
Definition original r :=
  match r with
  | Keep i => [i]
  | RemoveMove d => [Move d d]
  | Overwrite d x y => [Imm d x; Imm d y]
  | Fold d x op v => [Imm d x; Binary op d d d]
  | RemoveBranch a x t => [Imm a x; Branch a t] end.
Definition replacement r :=
  match r with
  | Keep i => [i]
  | RemoveMove _ => [Pad 1]
  | Overwrite d x y => [Pad 8; Imm d y]
  | Fold d x op v => [Imm d v; Pad 2]
  | RemoveBranch a x t => [Imm a x; Pad 8] end.
Definition rule_check r :=
  match r with
  | Fold _ x op v => match eval_bin op (word x) (word x) with Some z => N.eqb z v | None => false end
  | RemoveBranch _ x _ => N.eqb (word x) 0
  | _ => true end.
Record block := Block { block_pc : nat; block_rule : rewrite_rule }.
Definition cutpoint bs p := existsb (fun b => Nat.eqb p (block_pc b)) bs.
Definition outgoing bs p i :=
  match i with
  | Halt | Trap | Ret => true
  | Indirect _ => false
  | Jump t => cutpoint bs t
  | Branch _ t | Call t => cutpoint bs t && cutpoint bs (p + width i)
  | _ => cutpoint bs (p + width i) end.
Definition block_check c d bs b :=
  let p := block_pc b in let r := block_rule b in
  boundary c p && rule_check r && layout_check c p (original r) && layout_check d p (replacement r) &&
  match r with
  | Keep i => outgoing bs p i
  | _ => cutpoint bs (p + code_size (original r)) end.
Definition certificate_check c d bs :=
  verify c && verify d && metadata_check c d && cutpoint bs 0 && forallb (block_check c d bs) bs.
Inductive counted c : nat -> state -> state -> Prop :=
| counted_zero s : counted c 0 s s
| counted_step n s t u : transition c s t -> counted c n t u -> counted c (S n) s u.
Lemma counted_steps c n s t : counted c n s t -> steps c s t.
Proof. intro H. induction H; eauto using steps. Qed.
Lemma steps_counted c s t : steps c s t -> exists n, counted c n s t.
Proof.
  intro H. induction H.
  - exists 0. constructor.
  - destruct IHsteps as [n C]. exists (S n). eauto using counted.
Qed.
Lemma counted_canonical c n s t : counted c n s t -> canonical s -> canonical t.
Proof. intro H. induction H; eauto using transition_canonical. Qed.
Lemma transition_running c s t : transition c s t -> mode s = Running.
Proof. intro H. inversion H; assumption. Qed.
Lemma counted_prefix c k s a : counted c k s a ->
  forall n z, counted c n s z -> mode z <> Running ->
  exists m, n = k + m /\ counted c m a z.
Proof.
  intro H. induction H; intros n0 z E Z.
  - exists n0. auto.
  - inversion E as [|n' s' t' z' T' E']; subst.
    + exfalso. apply Z. eauto using transition_running.
    + assert (t = t') by (eapply transition_deterministic; eauto). subst t'.
      destruct (IHcounted _ _ E' Z) as [m [L C]]. exists m. split; auto. lia.
Qed.
Lemma guards_refl c p : same_guards c c p.
Proof. repeat split; reflexivity. Qed.
Lemma sequence_equal_states c xs s t : states_equal s t ->
  states_equal (execute_sequence c s xs) (execute_sequence c t xs).
Proof.
  revert s t. induction xs; intros s t E; cbn; auto.
  pose proof (proj1 (proj2 E)) as M. rewrite <- M. destruct (mode s).
  - apply IHxs. apply execute_equal; [exact E | apply guards_refl].
  - exact E.
  - exact E.
Qed.
Lemma straight_independent c d s i : straight i -> execute c s i = execute d s i.
Proof. destruct i; cbn [straight]; intros H; try contradiction; reflexivity. Qed.
Lemma sequence_independent c d xs s : Forall straight xs ->
  execute_sequence c s xs = execute_sequence d s xs.
Proof.
  intro H. revert s. induction H; intro s; cbn; auto.
  destruct (mode s); auto. rewrite (straight_independent c d s x H). apply IHForall.
Qed.
Lemma canonical_word s r : canonical s -> word (regs s r) = regs s r.
Proof. intros [R _]. unfold word. apply N.mod_small. apply R. Qed.
Lemma rule_sound c d r s t :
  rule_check r = true -> mode s = Running -> canonical s ->
  states_equal s t -> same_guards c d (pc s) ->
  states_equal (execute_sequence c s (original r)) (execute_sequence d t (replacement r)).
Proof.
  intros V M W E G. destruct r.
  - cbn [original replacement execute_sequence]. rewrite M, <- (proj1 (proj2 E)).
    rewrite M. now apply execute_equal.
  - assert (Q : equivalent_state (execute_sequence c s [Move d0 d0]) (execute_sequence c s [Pad 1])).
    { apply redundant_move; auto. apply canonical_word. exact W. }
    apply equivalent_states in Q.
    rewrite (sequence_independent c d [Pad 1] s ltac:(repeat constructor)) in Q.
    eapply states_equal_trans; [exact Q | apply sequence_equal_states; exact E].
  - pose proof (equivalent_states _ _ (dead_store c s d0 x y M)) as Q.
    rewrite (sequence_independent c d [Pad 8; Imm d0 y] s ltac:(repeat constructor)) in Q.
    eapply states_equal_trans; [exact Q | apply sequence_equal_states; exact E].
  - cbn [rule_check] in V. destruct (eval_bin op (word x) (word x)) eqn:A; try discriminate.
    apply N.eqb_eq in V. subst n.
    pose proof (equivalent_states _ _ (constant_propagation c s d0 x op v M A)) as Q.
    rewrite (sequence_independent c d [Imm d0 v; Pad 2] s ltac:(repeat constructor)) in Q.
    eapply states_equal_trans; [exact Q | apply sequence_equal_states; exact E].
  - cbn [rule_check] in V. apply N.eqb_eq in V.
    pose proof (branch_false c s a x target M V) as Q.
    rewrite (sequence_independent c d [Imm a x; Pad 8] s ltac:(repeat constructor)) in Q.
    cbn [original replacement]. rewrite Q. apply sequence_equal_states. exact E.
Qed.
Lemma counted_one c s i : mode s = Running -> decode c (pc s) = Some i ->
  counted c 1 s (execute c s i).
Proof. intros M D. eapply counted_step; [eapply decoded; eauto | constructor]. Qed.
Lemma counted_two c s i j : mode s = Running -> decode c (pc s) = Some i ->
  mode (execute c s i) = Running -> decode c (pc (execute c s i)) = Some j ->
  counted c 2 s (execute c (execute c s i) j).
Proof. intros M D R E. eapply counted_step; [eapply decoded; eauto | now apply counted_one]. Qed.
Lemma original_count c s r : mode s = Running -> expression_layout c (pc s) (original r) ->
  counted c (length (original r)) s (execute_sequence c s (original r)).
Proof.
  intros M L. destruct r; cbn [original expression_layout] in L;
  cbn [original execute_sequence length]; rewrite M;
  destruct L as [D L]; try solve [now apply counted_one];
  destruct L as [D' _]; cbn [execute write_reg at_pc mode];
  lazymatch type of D with decode _ _ = Some ?i =>
    lazymatch type of D' with decode _ _ = Some ?j =>
      apply (counted_two c s i j); [exact M | exact D | reflexivity | exact D']
    end end.
Qed.
Lemma replacement_count c s r : mode s = Running -> expression_layout c (pc s) (replacement r) ->
  counted c (length (original r)) s (execute_sequence c s (replacement r)).
Proof.
  intros M L. destruct r; cbn [replacement expression_layout] in L;
  cbn [original replacement execute_sequence length]; rewrite M;
  destruct L as [D L]; try solve [now apply counted_one];
  try solve [cbn; now apply counted_one];
  destruct L as [D' _]; cbn [execute write_reg at_pc mode];
  lazymatch type of D with decode _ _ = Some ?i =>
    lazymatch type of D' with decode _ _ = Some ?j =>
      apply (counted_two c s i j); [exact M | exact D | reflexivity | exact D']
    end end.
Qed.
Definition valid_position bs s :=
  cutpoint bs (pc s) = true /\ Forall (fun f => cutpoint bs (return_pc f) = true) (frames s).
Lemma outgoing_position c bs s i : valid_position bs s -> outgoing bs (pc s) i = true ->
  valid_position bs (execute c s i).
Proof.
  intros [P F] O. destruct i; cbn [outgoing execute] in *; try discriminate;
  unfold transfer, at_pc, write_reg, finish; cbn;
  repeat match goal with H : (_ && _) = true |- _ => apply andb_true_iff in H; destruct H end;
  repeat match goal with
  | |- context [if ?b then _ else _] => destruct b eqn:?
  | |- context [match ?x with Some _ => _ | None => _ end] => destruct x eqn:?
  | |- context [match frames s with _ => _ end] => destruct (frames s) eqn:?
  end;
  unfold valid_position; cbn; try solve [split; auto];
  try solve [split; [assumption | constructor; assumption]];
  inversion F; subst; auto.
Qed.
Lemma fragment_position c bs s r :
  mode s = Running -> valid_position bs s -> rule_check r = true ->
  (match r with Keep i => outgoing bs (pc s) i | _ => cutpoint bs (pc s + code_size (original r)) end) = true ->
  valid_position bs (execute_sequence c s (original r)).
Proof.
  intros M P R O. destruct r.
  - cbn [original execute_sequence]. rewrite M. now apply outgoing_position.
  - destruct P as [P F]. cbn [original execute_sequence]. rewrite M.
    unfold valid_position. cbn [execute write_reg at_pc pc frames code_size width] in *.
    auto.
  - destruct P as [P F]. cbn [original execute_sequence]. rewrite M.
    unfold valid_position. cbn [execute write_reg at_pc pc frames mode code_size width] in *.
    split; auto. replace (pc s + 10 + 10) with (pc s + 20) by lia. exact O.
  - destruct P as [P F]. cbn [rule_check] in R.
    destruct (eval_bin op (word x) (word x)) eqn:E; try discriminate.
    cbn [original execute_sequence]. rewrite M.
    cbn [execute write_reg at_pc pc frames mode regs]. rewrite !put_same, E.
    unfold valid_position. cbn [write_reg at_pc pc frames code_size width] in *.
    split; auto. replace (pc s + 10 + 4) with (pc s + 14) by lia. exact O.
  - destruct P as [P F]. cbn [rule_check] in R. apply N.eqb_eq in R.
    cbn [original execute_sequence]. rewrite M.
    cbn [execute write_reg at_pc pc frames mode regs]. rewrite put_same, R.
    unfold valid_position. cbn [at_pc pc frames code_size width] in *.
    split; auto. replace (pc s + 10 + 10) with (pc s + 20) by lia. exact O.
Qed.
Lemma cutpoint_witness bs p : cutpoint bs p = true -> exists b, In b bs /\ p = block_pc b.
Proof.
  unfold cutpoint. rewrite existsb_exists. intros [b [I E]].
  apply Nat.eqb_eq in E. exists b. auto.
Qed.
Lemma checked_block c d bs b : block_check c d bs b = true ->
  boundary c (block_pc b) = true /\ rule_check (block_rule b) = true /\
  expression_layout c (block_pc b) (original (block_rule b)) /\
  expression_layout d (block_pc b) (replacement (block_rule b)) /\
  (match block_rule b with Keep i => outgoing bs (block_pc b) i
   | _ => cutpoint bs (block_pc b + code_size (original (block_rule b))) end) = true.
Proof.
  unfold block_check. rewrite !andb_true_iff. intros [[[[B R] L] T] O].
  repeat split; auto using layout_check_sound.
Qed.
Lemma certificate_parts c d bs : certificate_check c d bs = true ->
  metadata_check c d = true /\ cutpoint bs 0 = true /\ forallb (block_check c d bs) bs = true.
Proof. unfold certificate_check. rewrite !andb_true_iff. tauto. Qed.
Theorem checked_block_simulation c d bs s t :
  certificate_check c d bs = true -> valid_position bs s -> canonical s ->
  mode s = Running -> states_equal s t ->
  exists k s' t', 0 < k /\ counted c k s s' /\ counted d k t t' /\
                  states_equal s' t' /\ valid_position bs s'.
Proof.
  intros V P W M E. destruct (certificate_parts c d bs V) as [Meta [_ All]].
  destruct (cutpoint_witness bs (pc s) (proj1 P)) as [b [I Pc]].
  apply forallb_forall with (x := b) in All; auto.
  destruct (checked_block c d bs b All) as [B [R [L [T O]]]].
  rewrite <- Pc in B, L, T, O.
  exists (length (original (block_rule b))),
         (execute_sequence c s (original (block_rule b))),
         (execute_sequence d t (replacement (block_rule b))).
  split; [destruct (block_rule b); cbn; lia |].
  split; [now apply original_count |].
  split.
  - apply replacement_count; [now rewrite <- (proj1 (proj2 E)) |]. now rewrite <- (proj1 E).
  - split.
    + apply rule_sound; auto. now apply metadata_guards.
    + now apply fragment_position.
Qed.
Theorem optimisation_forward c d bs : certificate_check c d bs = true ->
  forall n s z t, counted c n s z -> mode z <> Running ->
  valid_position bs s -> canonical s -> states_equal s t ->
  exists u, steps d t u /\ states_equal z u.
Proof.
  intros V n. induction n using lt_wf_ind.
  intros s z t Run End Pos Can Eq. destruct n.
  - inversion Run; subst. exists t. split; [constructor | exact Eq].
  - assert (M : mode s = Running) by (inversion Run; eauto using transition_running).
    destruct (checked_block_simulation c d bs s t V Pos Can M Eq)
      as [k [s' [t' [K [A [B [E P]]]]]]].
    destruct (counted_prefix c k s s' A (S n) z Run End) as [m [N Tail]].
    assert (m < S n) by lia.
    destruct (H m H0 s' z t' Tail End P (counted_canonical c k s s' A Can) E) as [u [T U]].
    exists u. split; auto. exact (steps_trans d t t' u (counted_steps d k t t' B) T).
Qed.
Theorem whole_program_optimisation c d bs z :
  certificate_check c d bs = true -> steps c initial z -> mode z <> Running ->
  exists u, steps d initial u /\ states_equal z u.
Proof.
  intros V Run End. destruct (steps_counted c initial z Run) as [n N].
  eapply optimisation_forward; eauto using initial_canonical, states_equal_refl.
  split; [exact (proj1 (proj2 (certificate_parts c d bs V))) | constructor].
Qed.
Theorem optimisation_backward c d bs : certificate_check c d bs = true ->
  forall n s t z, counted d n t z -> mode z <> Running ->
  valid_position bs s -> canonical s -> states_equal s t ->
  exists u, steps c s u /\ states_equal u z.
Proof.
  intros V n. induction n using lt_wf_ind.
  intros s t z Run End Pos Can Eq. destruct n.
  - inversion Run; subst. exists s. split; [constructor | exact Eq].
  - assert (M : mode s = Running).
    { rewrite (proj1 (proj2 Eq)). inversion Run; eauto using transition_running. }
    destruct (checked_block_simulation c d bs s t V Pos Can M Eq)
      as [k [s' [t' [K [A [B [E P]]]]]]].
    destruct (counted_prefix d k t t' B (S n) z Run End) as [m [N Tail]].
    assert (m < S n) by lia.
    destruct (H m H0 s' t' z Tail End P (counted_canonical c k s s' A Can) E) as [u [T U]].
    exists u. split; auto. exact (steps_trans c s s' u (counted_steps c k s s' A) T).
Qed.
Theorem whole_program_optimisation_reverse c d bs z :
  certificate_check c d bs = true -> steps d initial z -> mode z <> Running ->
  exists u, steps c initial u /\ states_equal u z.
Proof.
  intros V Run End. destruct (steps_counted d initial z Run) as [n N].
  eapply optimisation_backward; eauto using initial_canonical, states_equal_refl.
  split; [exact (proj1 (proj2 (certificate_parts c d bs V))) | constructor].
Qed.
Definition candidate_rules c p i :=
  match i with
  | Move d a => if Nat.eqb d a then [RemoveMove d; Keep i] else [Keep i]
  | Imm d x =>
      match decode c (p + 10) with
      | Some (Imm e y) => if Nat.eqb d e then [Overwrite d x y; Keep i] else [Keep i]
      | Some (Binary op e a b) =>
          if Nat.eqb d e && Nat.eqb d a && Nat.eqb d b then
            match eval_bin op (word x) (word x) with
            | Some v => [Fold d x op v; Keep i] | None => [Keep i] end
          else [Keep i]
      | Some (Branch a t) => if Nat.eqb d a then [RemoveBranch a x t; Keep i] else [Keep i]
      | _ => [Keep i] end
  | _ => [Keep i] end.
Definition choose_rule c d p i :=
  find (fun r => rule_check r && layout_check c p (original r) && layout_check d p (replacement r))
       (candidate_rules c p i).
Fixpoint discover fuel c d p : option (list block) :=
  if Nat.eqb p (length c) then Some [] else
  match fuel with
  | 0 => None
  | S fuel =>
      match decode c p with
      | None => None
      | Some i =>
          match choose_rule c d p i with
          | None => None
          | Some r => option_map (fun bs => Block p r :: bs)
                                 (discover fuel c d (p + code_size (original r))) end end
  end.
Definition validate_optimisation c d :=
  if list_eq_dec Nat.eq_dec c d then true else
  match discover (length c) c d 0 with
  | Some bs => certificate_check c d bs | None => false end.
Theorem validated_optimisation c d z : validate_optimisation c d = true ->
  steps c initial z -> mode z <> Running -> exists u, steps d initial u /\ states_equal z u.
Proof.
  unfold validate_optimisation. destruct (list_eq_dec Nat.eq_dec c d) as [E|E].
  - subst d. intros _ Run End. exists z. auto using states_equal_refl.
  - destruct (discover (length c) c d 0) eqn:D; try discriminate.
    apply whole_program_optimisation.
Qed.
Theorem validated_optimisation_reverse c d z : validate_optimisation c d = true ->
  steps d initial z -> mode z <> Running -> exists u, steps c initial u /\ states_equal u z.
Proof.
  unfold validate_optimisation. destruct (list_eq_dec Nat.eq_dec c d) as [E|E].
  - subst d. intros _ Run End. exists z. auto using states_equal_refl.
  - destruct (discover (length c) c d 0) eqn:D; try discriminate.
    apply whole_program_optimisation_reverse.
Qed.
Definition diverges c := forall z, steps c initial z -> mode z = Running.
Theorem validated_optimisation_divergence c d :
  validate_optimisation c d = true -> (diverges c <-> diverges d).
Proof.
  intro V. split; intros D z Run; destruct (mode z) eqn:M; auto; exfalso.
  - destruct (validated_optimisation_reverse c d z V Run ltac:(congruence)) as [u [U E]].
    pose proof (D u U). destruct E as [_ [E _]]. congruence.
  - destruct (validated_optimisation_reverse c d z V Run ltac:(congruence)) as [u [U E]].
    pose proof (D u U). destruct E as [_ [E _]]. congruence.
  - destruct (validated_optimisation c d z V Run ltac:(congruence)) as [u [U E]].
    pose proof (D u U). destruct E as [_ [E _]]. congruence.
  - destruct (validated_optimisation c d z V Run ltac:(congruence)) as [u [U E]].
    pose proof (D u U). destruct E as [_ [E _]]. congruence.
Qed.
Inductive optimisation_pipeline : list nat -> list nat -> Prop :=
| pipeline_identity c : optimisation_pipeline c c
| pipeline_pass c d e : validate_optimisation c d = true -> optimisation_pipeline d e ->
    optimisation_pipeline c e.
Theorem optimisation_pipeline_correct c d : optimisation_pipeline c d ->
  forall z, steps c initial z -> mode z <> Running ->
  exists u, steps d initial u /\ states_equal z u.
Proof.
  intro H. induction H; intros z Run End.
  - exists z. auto using states_equal_refl.
  - destruct (validated_optimisation c d z H Run End) as [m [M E]].
    assert (mode m <> Running) by (destruct E as [_ [E _]]; congruence).
    destruct (IHoptimisation_pipeline m M H1) as [u [U F]].
    exists u. split; eauto using states_equal_trans.
Qed.
Theorem optimisation_pipeline_divergence c d :
  optimisation_pipeline c d -> (diverges c <-> diverges d).
Proof.
  intro H. induction H; try tauto.
  pose proof (validated_optimisation_divergence c d H). tauto.
Qed.
Theorem optimisation_pipeline_reverse c d : optimisation_pipeline c d ->
  forall z, steps d initial z -> mode z <> Running ->
  exists u, steps c initial u /\ states_equal u z.
Proof.
  intro H. induction H; intros z Run End.
  - exists z. auto using states_equal_refl.
  - destruct (IHoptimisation_pipeline z Run End) as [m [M E]].
    assert (EndM : mode m <> Running) by (destruct E as [_ [E _]]; congruence).
    destruct (validated_optimisation_reverse c d m H M EndM) as [u [U F]].
    exists u. split; eauto using states_equal_trans.
Qed.
