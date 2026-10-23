From Stdlib Require Import List NArith Arith Bool Lia.
From IceVM Require Import Syntax State Semantics Interpreter Verifier Source Compiler.
Import ListNotations.
Definition straight i :=
  match i with
  | Imm _ _ | Move _ _ | Binary _ _ _ _ | Load _ _ | Store _ _
  | Alloc _ _ | Mark _ | Reset _ | Entry | Nop | Pad _ => True
  | _ => False end.
Local Opaque memory_size stack_size.
Lemma straight_pc code s i : straight i -> mode (execute code s i) = Running ->
  pc (execute code s i) = pc s + width i.
Proof.
  destruct i; cbn [straight]; try contradiction;
  cbn [execute]; unfold write_reg, at_pc, finish; cbn;
  repeat match goal with
  | |- context [if ?b then _ else _] => destruct b
  | |- context [match ?x with Some _ => _ | None => _ end] => destruct x
  end; cbn; intros; try discriminate; reflexivity.
Qed.
Theorem sequence_execution code xs s :
  expression_layout code (pc s) xs -> Forall straight xs ->
  steps code s (execute_sequence code s xs).
Proof.
  revert s. induction xs as [|i xs IH]; intros s L F; cbn; try constructor.
  inversion F; subst. destruct (mode s) eqn:M; try constructor.
  destruct L as [D L].
  eapply steps_cons; [eapply decoded; eauto |].
  destruct (mode (execute code s i)) eqn:T.
  - apply IH; auto. now rewrite (straight_pc code s i H1 T).
  - destruct xs; cbn; try rewrite T; constructor.
  - destruct xs; cbn; try rewrite T; constructor.
Qed.
Lemma compiled_pure_straight e d xs :
  variables_below e d -> compile_expression e d = Some xs -> Forall straight xs.
Proof.
  revert d xs. induction e; cbn; intros d xs B C; try contradiction.
  - inversion C; repeat constructor.
  - inversion C; repeat constructor.
  - destruct B as [Ba Bb]. destruct (compile_expression e1 d) as [lhs|] eqn:A; try discriminate.
    destruct (compile_expression e2 (S d)) as [rhs|] eqn:E; try discriminate.
    inversion C; subst. apply Forall_app. split.
    + eapply IHe1; eauto.
    + apply Forall_app. split; [|repeat constructor].
      apply (IHe2 (S d) rhs).
      * eapply variables_monotone; [exact Bb | lia].
      * exact E.
Qed.
Theorem compiled_expression_execution code e d xs s v :
  compile_expression e d = Some xs -> variables_below e d ->
  pure_value (fun x => regs s (S x)) e = Some v -> mode s = Running ->
  expression_layout code (pc s) xs ->
  exists t, steps code s t /\ expression_result s t d v xs.
Proof.
  intros C B V M L. exists (execute_sequence code s xs). split.
  - apply sequence_execution; auto. eapply compiled_pure_straight; eauto.
  - eapply compile_pure_correct; eauto.
Qed.
Definition machine_valid code s := well_formed s /\ canonical s /\ structural code s.
Lemma machine_valid_transition code s t : verify code = true -> machine_valid code s ->
  transition code s t -> machine_valid code t.
Proof.
  intros V [W [C S]] T. split; [eapply transition_well_formed; eauto |].
  split; [eapply transition_canonical; eauto | eapply verifier_sound; eauto].
Qed.
Lemma machine_valid_steps code s t : verify code = true -> machine_valid code s ->
  steps code s t -> machine_valid code t.
Proof. intros V I E. revert I. induction E; eauto using machine_valid_transition. Qed.
Lemma execution_one code s i : mode s = Running -> decode code (pc s) = Some i ->
  steps code s (execute code s i).
Proof. intros M D. eapply steps_cons; [eapply decoded; eauto | constructor]. Qed.
Lemma checked_call code s target : verify code = true -> machine_valid code s ->
  decode code (pc s) = Some (Call target) ->
  call_target code target = true /\ local_target code (pc s) (pc s + 9) = true.
Proof.
  intros V [_ [_ [B _]]] D. pose proof (checked_boundary code (pc s) V B) as H.
  unfold check_at in H. rewrite D in H. now apply andb_true_iff in H.
Qed.
Lemma canonical_register_word s r : canonical s -> word (regs s r) = regs s r.
Proof. intros [H _]. unfold word. apply N.mod_small. apply H. Qed.
Definition expression_run code s e d v m h t :=
  steps code s t /\ mode t = Running /\ pc t = pc s + expression_width e /\
  regs t d = word v /\
  (forall r, 0 < r < d -> regs t r = regs s r) /\
  mem t = m /\ frontier t = h /\ frames t = frames s.
Definition statement_run code root body s result env m h t :=
  steps code s t /\ mode t = Running /\ locals_match env (regs t) /\
  mem t = m /\ frontier t = h /\ frames t = frames s /\
  match result with
  | None => pc t = pc s + statement_width body
  | Some v => regs t 0 = word v /\ decode code (pc t) = Some (exit_instruction root)
  end.
Lemma expression_locals env code s e d v m h t : 9 <= d ->
  locals_match env (regs s) -> expression_run code s e d v m h t -> locals_match env (regs t).
Proof. intros D L [_ [_ [_ [_ [P _]]]]] n N. rewrite P by lia. now apply L. Qed.
Lemma put_below r d v n : n < d -> put r d v n = r n.
Proof. intro H. apply put_other. lia. Qed.
Lemma locals_assignment env r n v : n < 8 -> locals_match env r ->
  locals_match (put env n v) (put r (S n) v).
Proof.
  intros N L k K. unfold put. cbn [Nat.eqb]. destruct (Nat.eqb k n); auto using word_idempotent.
Qed.
Lemma expression_head_valid fs e d : valid_expression fs e d = true -> d < 15.
Proof. destruct e; cbn; rewrite andb_true_iff; intros [H _]; now apply Nat.ltb_lt. Qed.
Lemma expression_eval_word fs depth env e m h v m' h' :
  evaluates_expression (source_lookup fs) depth env e m h v m' h' -> word v = v.
Proof. apply (proj1 (evaluations_canonical (source_lookup fs))). Qed.
Definition expression_compiles fs code depth env e m h v m' h' :=
  forall s d, machine_valid code s -> mode s = Running -> length (frames s) = depth ->
  locals_match env (regs s) -> mem s = m -> frontier s = h -> 9 <= d ->
  valid_expression (length fs) e d = true ->
  expression_layout code (pc s) (emit_expression (address_of fs) e d) ->
  exists t, expression_run code s e d v m' h' t.
Definition statement_compiles fs code depth env body m h result env' m' h' :=
  forall s root, machine_valid code s -> mode s = Running -> length (frames s) = depth ->
  locals_match env (regs s) -> mem s = m -> frontier s = h ->
  valid_statement (length fs) body = true ->
  expression_layout code (pc s) (emit_statement (address_of fs) root body (pc s)) ->
  exists t, statement_run code root body s result env' m' h' t.
Lemma emit_literal_correct fs code depth env n m h :
  expression_compiles fs code depth env (Literal n) m h (word n) m h.
Proof.
  intros s d I M D L Mem F B V [Dec _].
  exists (execute code s (Imm d (word n))). unfold expression_run.
  split; [now apply execution_one |].
  cbn [execute write_reg at_pc mode regs pc mem frontier frames expression_width width].
  rewrite put_same, word_idempotent. repeat split; auto.
  intros r R. apply put_other. lia.
Qed.
Lemma emit_local_correct fs code depth env n m h :
  expression_compiles fs code depth env (Local n) m h (word (env n)) m h.
Proof.
  intros s d I M D L Mem F B V [Dec _].
  assert (N : n < 8) by (cbn in V; apply andb_true_iff in V; destruct V; now apply Nat.ltb_lt).
  exists (execute code s (Move d (S n))). unfold expression_run.
  split; [now apply execution_one |].
  cbn [execute write_reg at_pc mode regs pc mem frontier frames expression_width width].
  rewrite put_same, (L n N), !word_idempotent. repeat split; auto.
  intros r R. apply put_other. lia.
Qed.
Lemma emit_watermark_correct fs code depth env m h :
  expression_compiles fs code depth env Watermark m h (word (N.of_nat h)) m h.
Proof.
  intros s d I M D L Mem F B V [Dec _].
  exists (execute code s (Mark d)). unfold expression_run.
  split; [now apply execution_one |].
  cbn [execute write_reg at_pc mode regs pc mem frontier frames expression_width width].
  rewrite put_same, F, word_idempotent. repeat split; auto.
  intros r R. apply put_other. lia.
Qed.
Definition pair_run code s a b d x y m h t :=
  steps code s t /\ mode t = Running /\ pc t = pc s + expression_width a + expression_width b /\
  regs t d = word x /\ regs t (S d) = word y /\
  (forall r, 0 < r < d -> regs t r = regs s r) /\
  mem t = m /\ frontier t = h /\ frames t = frames s.
Lemma emit_pair_correct fs code depth env a b m h x m1 h1 y m2 h2 :
  compilation_check fs code = true ->
  expression_compiles fs code depth env a m h x m1 h1 ->
  expression_compiles fs code depth env b m1 h1 y m2 h2 ->
  forall s d, machine_valid code s -> mode s = Running -> length (frames s) = depth ->
  locals_match env (regs s) -> mem s = m -> frontier s = h -> 9 <= d ->
  valid_expression (length fs) a d = true -> valid_expression (length fs) b (S d) = true ->
  expression_layout code (pc s) (emit_expression (address_of fs) a d) ->
  expression_layout code (pc s + expression_width a) (emit_expression (address_of fs) b (S d)) ->
  exists t, pair_run code s a b d x y m2 h2 t.
Proof.
  intros C A B s d I M D L Mem F Bound Va Vb La Lb.
  destruct (A s d I M D L Mem F Bound Va La) as [s1 E1].
  pose proof (expression_locals env code s a d x m1 h1 s1 Bound L E1) as L1.
  destruct E1 as [T1 [M1 [P1 [R1 [Below1 [Mem1 [F1 S1]]]]]]].
  assert (I1 : machine_valid code s1) by (eapply machine_valid_steps; eauto using compilation_verified).
  assert (D1 : length (frames s1) = depth) by congruence.
  assert (Lb1 : expression_layout code (pc s1) (emit_expression (address_of fs) b (S d))) by now rewrite P1.
  destruct (B s1 (S d) I1 M1 D1 L1 Mem1 F1 ltac:(lia) Vb Lb1) as [s2 E2].
  destruct E2 as [T2 [M2 [P2 [R2 [Below2 [Mem2 [F2 S2]]]]]]].
  exists s2. unfold pair_run. split; [eapply steps_trans; eauto |].
  split; [exact M2 |]. split; [lia |]. split.
  - rewrite Below2 by lia. exact R1.
  - split; [exact R2 |]. split.
    + intros r R. rewrite Below2 by lia. now apply Below1.
    + repeat split; auto. congruence.
Qed.
Lemma emit_operation_correct fs code depth env op a b m h x m1 h1 y m2 h2 z :
  compilation_check fs code = true -> word x = x -> word y = y -> eval_bin op x y = Some z ->
  expression_compiles fs code depth env a m h x m1 h1 ->
  expression_compiles fs code depth env b m1 h1 y m2 h2 ->
  expression_compiles fs code depth env (Operation op a b) m h (word z) m2 h2.
Proof.
  intros C X Y Z A B s d I M D L Mem F Bound V Layout.
  cbn [valid_expression] in V. rewrite !andb_true_iff in V. destruct V as [_ [Va Vb]].
  cbn [emit_expression] in Layout. apply layout_append in Layout. destruct Layout as [La Rest].
  rewrite expression_size in Rest. apply layout_append in Rest. destruct Rest as [Lb End].
  rewrite expression_size in End. cbn [expression_layout] in End. destruct End as [Dec _].
  destruct (emit_pair_correct fs code depth env a b m h x m1 h1 y m2 h2 C A B
    s d I M D L Mem F Bound Va Vb La Lb) as [s2 E].
  destruct E as [T [M2 [P [R1 [R2 [Below [Mem2 [F2 S2]]]]]]]].
  assert (Dec2 : decode code (pc s2) = Some (Binary op d d (S d))) by now rewrite P.
  pose proof (execution_one code s2 (Binary op d d (S d)) M2 Dec2) as Last.
  exists (execute code s2 (Binary op d d (S d))). unfold expression_run.
  split; [eapply steps_trans; eauto |].
  cbn [execute]. rewrite R1, R2, X, Y, Z.
  cbn [write_reg at_pc mode pc regs mem frontier frames expression_width width].
  rewrite put_same, word_idempotent. split; [reflexivity |]. split; [lia |].
  split; [reflexivity |]. split.
  - intros r H. rewrite put_other by lia. now apply Below.
  - repeat split; auto.
Qed.
Lemma emit_read_correct fs code depth env a m h x m1 h1 :
  word x = x -> N.to_nat x + 8 <= h1 ->
  expression_compiles fs code depth env a m h x m1 h1 ->
  expression_compiles fs code depth env (Read a) m h (word (read64 m1 (N.to_nat x))) m1 h1.
Proof.
  intros X Bound A s d I M D L Mem F B V Layout.
  cbn [valid_expression] in V. apply andb_true_iff in V. destruct V as [_ Va].
  cbn [emit_expression] in Layout. apply layout_append in Layout. destruct Layout as [La End].
  rewrite expression_size in End. cbn [expression_layout] in End. destruct End as [Dec _].
  destruct (A s d I M D L Mem F B Va La) as [s1 E].
  destruct E as [T [M1 [P [R [Below [Mem1 [F1 S1]]]]]]].
  assert (Dec1 : decode code (pc s1) = Some (Load d d)) by now rewrite P.
  pose proof (execution_one code s1 (Load d d) M1 Dec1) as Last.
  exists (execute code s1 (Load d d)). unfold expression_run.
  split; [eapply steps_trans; eauto |].
  cbn [execute]. rewrite R, X, F1.
  assert (Check : (N.to_nat x + 8 <=? h1) = true) by now apply Nat.leb_le.
  rewrite Check. cbn [write_reg at_pc mode pc regs mem frontier frames expression_width width].
  rewrite put_same, Mem1, word_idempotent. split; [reflexivity |]. split; [lia |].
  split; [reflexivity |]. split.
  - intros r H. rewrite put_other by lia. now apply Below.
  - repeat split; auto.
Qed.
Lemma emit_new_correct fs code depth env a m h x m1 h1 :
  word x = x -> h1 + N.to_nat x <= memory_size ->
  expression_compiles fs code depth env a m h x m1 h1 ->
  expression_compiles fs code depth env (New a) m h (word (N.of_nat h1))
    (clear m1 h1 (h1 + N.to_nat x)) (h1 + N.to_nat x).
Proof.
  intros X Bound A s d I M D L Mem F B V Layout.
  cbn [valid_expression] in V. apply andb_true_iff in V. destruct V as [_ Va].
  cbn [emit_expression] in Layout. apply layout_append in Layout. destruct Layout as [La End].
  rewrite expression_size in End. cbn [expression_layout] in End. destruct End as [Dec _].
  destruct (A s d I M D L Mem F B Va La) as [s1 E].
  destruct E as [T [M1 [P [R [Below [Mem1 [F1 S1]]]]]]].
  assert (Dec1 : decode code (pc s1) = Some (Alloc d d)) by now rewrite P.
  pose proof (execution_one code s1 (Alloc d d) M1 Dec1) as Last.
  exists (execute code s1 (Alloc d d)). unfold expression_run.
  split; [eapply steps_trans; eauto |].
  cbn [execute]. rewrite R, X, F1.
  assert (Check : (h1 + N.to_nat x <=? memory_size) = true) by now apply Nat.leb_le.
  rewrite Check. cbn [write_reg at_pc mode pc regs mem frontier frames expression_width width].
  rewrite put_same, Mem1, word_idempotent. split; [reflexivity |]. split; [lia |].
  split; [reflexivity |]. split.
  - intros r H. rewrite put_other by lia. now apply Below.
  - repeat split; auto.
Qed.
Lemma comparison_result code s op d x y : mode s = Running ->
  regs s d = x -> regs s (S d) = y ->
  expression_result s (execute_sequence code s (comparison_code op d)) d
    (compare_values op x y) (comparison_code op d).
Proof.
  intros M X Y.
  assert (DS : Nat.eqb d (S d) = false) by (apply Nat.eqb_neq; lia).
  assert (SD : Nat.eqb (S d) d = false) by (apply Nat.eqb_neq; lia).
  destruct op; unfold expression_result;
  cbn [comparison_code execute_sequence app]; rewrite M;
  cbn [execute eval_bin write_reg at_pc mode pc regs mem frontier frames width code_size fst snd];
  rewrite ?X, ?Y;
  try rewrite !put_same;
  try (unfold put; rewrite ?Nat.eqb_refl, ?DS, ?SD);
  cbn [mode pc regs mem frontier frames execute execute_sequence eval_bin write_reg at_pc];
  unfold compare_values;
  repeat match goal with
  | |- context [N.eqb x y] => destruct (N.eqb x y) eqn:?
  | |- context [N.ltb x y] => destruct (N.ltb x y) eqn:?
  | |- context [N.ltb y x] => destruct (N.ltb y x) eqn:?
  end;
  cbn [word modulus]; repeat split; auto; try lia;
  intros n N; unfold put; rewrite ?Nat.eqb_refl, ?DS, ?SD;
  repeat match goal with
  | |- context [Nat.eqb n d] => rewrite (proj2 (Nat.eqb_neq n d) ltac:(lia))
  | |- context [Nat.eqb n (S d)] => rewrite (proj2 (Nat.eqb_neq n (S d)) ltac:(lia))
  end; reflexivity.
Qed.
Lemma comparison_size op d : code_size (comparison_code op d) =
  match op with CDifferent | CAtMost | CAtLeast => 18 | _ => 4 end.
Proof. now destruct op. Qed.
Lemma comparison_straight op d : Forall straight (comparison_code op d).
Proof. destruct op; repeat constructor. Qed.
Lemma emit_comparison_correct fs code depth env op a b m h x m1 h1 y m2 h2 :
  compilation_check fs code = true -> word x = x -> word y = y ->
  expression_compiles fs code depth env a m h x m1 h1 ->
  expression_compiles fs code depth env b m1 h1 y m2 h2 ->
  expression_compiles fs code depth env (Compare op a b) m h (word (compare_values op x y)) m2 h2.
Proof.
  intros C X Y A B s d I M D L Mem F Bound V Layout.
  cbn [valid_expression] in V. rewrite !andb_true_iff in V. destruct V as [_ [Va Vb]].
  cbn [emit_expression] in Layout. apply layout_append in Layout. destruct Layout as [La Rest].
  rewrite expression_size in Rest. apply layout_append in Rest. destruct Rest as [Lb End].
  rewrite expression_size in End.
  destruct (emit_pair_correct fs code depth env a b m h x m1 h1 y m2 h2 C A B
    s d I M D L Mem F Bound Va Vb La Lb) as [s2 E].
  destruct E as [T [M2 [P [R1 [R2 [Below [Mem2 [F2 S2]]]]]]]].
  rewrite X in R1. rewrite Y in R2.
  pose proof (comparison_result code s2 op d x y M2 R1 R2) as Q.
  destruct Q as [M3 [R3 [Below3 [P3 [Mem3 [F3 S3]]]]]].
  assert (Tail : steps code s2 (execute_sequence code s2 (comparison_code op d))).
  { apply sequence_execution; [now rewrite P | apply comparison_straight]. }
  exists (execute_sequence code s2 (comparison_code op d)). unfold expression_run.
  split; [eapply steps_trans; eauto |].
  split; [exact M3 |]. split.
  - rewrite comparison_size in P3. cbn [expression_width]. lia.
  - split; [now rewrite word_idempotent |]. split.
    + intros r H. rewrite Below3 by lia. now apply Below.
    + repeat split; congruence.
Qed.
Lemma prologue_straight : Forall straight (prologue false).
Proof. repeat constructor. Qed.
Lemma prologue_result code s x : mode s = Running -> regs s 15 = word x ->
  let t := execute_sequence code s (prologue false) in
  mode t = Running /\ pc t = pc s + 74 /\ mem t = mem s /\ frontier t = frontier s /\
  frames t = frames s /\ locals_match (put (fun _ => 0%N) 0 x) (regs t).
Proof.
  intros M X. cbn [prologue execute_sequence app map seq]. rewrite M.
  cbn [execute write_reg at_pc mode pc regs mem frontier frames width].
  repeat split; auto; try lia.
  intros n N. do 8 (destruct n as [|n]; [cbn [put]; rewrite ?X, ?word_idempotent; reflexivity |]). lia.
Qed.
Lemma perform_call code s target : call_target code target = true ->
  local_target code (pc s) (pc s + 9) = true -> length (frames s) < stack_size ->
  execute code s (Call target) =
  State target (regs s) (mem s) (frontier s) (Frame (pc s + 9) (regs s) :: frames s) Running.
Proof.
  intros C L S. cbn [execute at_pc pc width]. rewrite C, L. cbn -[Nat.ltb].
  assert (B : (length (frames s) <? stack_size) = true) by now apply Nat.ltb_lt.
  now rewrite B.
Qed.
Lemma perform_return code s p r fs : frames s = Frame p r :: fs -> boundary code p = true ->
  execute code s Ret = State p (put r 0 (regs s 0)) (mem s) (frontier s) fs Running.
Proof. intros F B. cbn [execute]. rewrite F. cbn [return_pc saved]. now rewrite B. Qed.
Lemma checked_jump code s target : verify code = true -> machine_valid code s ->
  decode code (pc s) = Some (Jump target) -> local_target code (pc s) target = true.
Proof.
  intros V [_ [_ [B _]]] D. pose proof (checked_boundary code (pc s) V B) as H.
  unfold check_at in H. now rewrite D in H.
Qed.
Lemma checked_branch code s reg target : verify code = true -> machine_valid code s ->
  decode code (pc s) = Some (Branch reg target) -> local_target code (pc s) target = true.
Proof.
  intros V [_ [_ [B _]]] D. pose proof (checked_boundary code (pc s) V B) as H.
  unfold check_at in H. rewrite D in H. apply andb_true_iff in H. tauto.
Qed.
Lemma emit_invoke_correct fs code depth env f a body m h x m1 h1 result env2 m2 h2 :
  compilation_check fs code = true -> word x = x -> nth_error fs f = Some body -> f <> 0 ->
  depth < stack_size ->
  expression_compiles fs code depth env a m h x m1 h1 ->
  statement_compiles fs code (S depth) (put (fun _ => 0%N) 0 x) body m1 h1 (Some result) env2 m2 h2 ->
  expression_compiles fs code depth env (Invoke f a) m h result m2 h2.
Proof.
  intros C X Lookup Nonroot Capacity Arg Body s d I M D L Mem F Bound V Layout.
  pose proof (compilation_verified fs code C) as Verified.
  assert (Upper : d < 15) by (eapply expression_head_valid; exact V).
  cbn [valid_expression] in V. rewrite !andb_true_iff in V. destruct V as [_ [[_ _] Va]].
  cbn [emit_expression] in Layout. apply layout_append in Layout. destruct Layout as [La Tail].
  rewrite expression_size in Tail. cbn [expression_layout width] in Tail.
  destruct Tail as [DecArg [DecCall [DecOut _]]].
  destruct (Arg s d I M D L Mem F Bound Va La) as [s1 E1].
  destruct E1 as [T1 [M1 [P1 [R1 [Below1 [Mem1 [F1 S1]]]]]]].
  set (s2 := execute code s1 (Move 15 d)).
  assert (T12 : steps code s1 s2) by (apply execution_one; auto; now rewrite P1).
  pose proof (steps_trans code s s1 s2 T1 T12) as T2.
  assert (I2 : machine_valid code s2) by (eapply machine_valid_steps; eauto).
  assert (M2 : mode s2 = Running) by reflexivity.
  assert (P2 : pc s2 = pc s1 + 3) by reflexivity.
  assert (S2 : frames s2 = frames s1) by reflexivity.
  assert (R15 : regs s2 15 = word x).
  { unfold s2. cbn [execute write_reg at_pc regs]. rewrite put_same, R1, word_idempotent. reflexivity. }
  assert (DC : decode code (pc s2) = Some (Call (address_of fs f))) by (rewrite P2, P1; exact DecCall).
  destruct (checked_call code s2 (address_of fs f) Verified I2 DC) as [Callable Local].
  assert (Cap : length (frames s2) < stack_size) by (rewrite S2, S1, D; exact Capacity).
  set (s3 := State (address_of fs f) (regs s2) (mem s2) (frontier s2)
                   (Frame (pc s2 + 9) (regs s2) :: frames s2) Running).
  assert (CallEq : execute code s2 (Call (address_of fs f)) = s3) by now apply perform_call.
  assert (T23 : steps code s2 s3) by (rewrite <- CallEq; now apply execution_one).
  pose proof (steps_trans code s s2 s3 T2 T23) as T3.
  destruct (checked_function fs code f body C Lookup) as [ValidBody [FunctionLayout FunctionTarget]].
  assert (FN : Nat.eqb f 0 = false) by now apply Nat.eqb_neq.
  rewrite FN in FunctionLayout. apply layout_append in FunctionLayout.
  destruct FunctionLayout as [PrologueLayout BodyLayout]. rewrite prologue_size in BodyLayout.
  cbn [prologue_width] in BodyLayout.
  set (s4 := execute_sequence code s3 (prologue false)).
  assert (T34 : steps code s3 s4) by (apply sequence_execution; auto using prologue_straight).
  pose proof (steps_trans code s s3 s4 T3 T34) as T4.
  destruct (prologue_result code s3 x eq_refl R15) as [M4 [P4 [Mem4 [F4 [S4 L4]]]]].
  fold s4 in M4, P4, Mem4, F4, S4, L4.
  assert (I4 : machine_valid code s4) by (exact (machine_valid_steps code s s4 Verified I T4)).
  assert (D4 : length (frames s4) = S depth) by (rewrite S4; cbn [s3 frames length]; rewrite S2, S1, D; reflexivity).
  assert (Mem4' : mem s4 = m1) by (rewrite Mem4; exact Mem1).
  assert (F4' : frontier s4 = h1) by (rewrite F4; exact F1).
  assert (Layout4 : expression_layout code (pc s4)
    (emit_statement (address_of fs) false body (pc s4))) by (rewrite P4; exact BodyLayout).
  destruct (Body s4 false I4 M4 D4 L4 Mem4' F4' ValidBody Layout4) as [s5 E5].
  destruct E5 as [T45 [M5 [L5 [Mem5 [F5 [S5 [R0 DecRet]]]]]]].
  pose proof (steps_trans code s s4 s5 T4 T45) as T5.
  assert (Frames5 : frames s5 = Frame (pc s2 + 9) (regs s2) :: frames s2) by (rewrite S5, S4; reflexivity).
  pose proof (local_boundary code (pc s2) (pc s2 + 9) Local) as ReturnBoundary.
  set (s6 := State (pc s2 + 9) (put (regs s2) 0 (word result)) (mem s5) (frontier s5) (frames s2) Running).
  assert (RetEq : execute code s5 Ret = s6).
  { rewrite (perform_return code s5 (pc s2 + 9) (regs s2) (frames s2) Frames5 ReturnBoundary), R0. reflexivity. }
  assert (T56 : steps code s5 s6) by (rewrite <- RetEq; apply execution_one; auto).
  pose proof (steps_trans code s s5 s6 T5 T56) as T6.
  assert (OutDecode : decode code (pc s6) = Some (Move d 0)).
  { cbn [s6 pc]. rewrite P2, P1. exact DecOut. }
  pose proof (execution_one code s6 (Move d 0) eq_refl OutDecode) as Last.
  exists (execute code s6 (Move d 0)). unfold expression_run.
  split; [eapply steps_trans; eauto |].
  cbn [execute s6 write_reg at_pc mode pc regs mem frontier frames expression_width width].
  rewrite !put_same, !word_idempotent. split; [reflexivity |]. split.
  - rewrite P2, P1. lia.
  - split; [reflexivity |]. split.
    + intros r H. rewrite !put_other by lia.
      unfold s2. cbn [execute write_reg at_pc regs]. rewrite put_other by lia. now apply Below1.
    + repeat split; auto.
Qed.
Lemma put_word r d v : put r d (word v) = put r d v.
Proof. unfold put. now rewrite word_idempotent. Qed.
Lemma emit_skip_correct fs code depth env m h :
  statement_compiles fs code depth env Skip m h None env m h.
Proof.
  intros s root I M D L Mem F V Layout. exists s. unfold statement_run.
  split; [constructor |]. repeat split; auto.
Qed.
Lemma emit_assign_correct fs code depth env n e m h x m1 h1 :
  expression_compiles fs code depth env e m h x m1 h1 ->
  statement_compiles fs code depth env (Assign n e) m h None (put env n x) m1 h1.
Proof.
  intros A s root I M D L Mem F V Layout.
  cbn [valid_statement] in V. apply andb_true_iff in V. destruct V as [N Va]. apply Nat.ltb_lt in N.
  cbn [emit_statement] in Layout. apply layout_append in Layout. destruct Layout as [La End].
  rewrite expression_size in End. cbn [expression_layout] in End. destruct End as [Dec _].
  destruct (A s 9 I M D L Mem F ltac:(lia) Va La) as [s1 E].
  pose proof (expression_locals env code s e 9 x m1 h1 s1 ltac:(lia) L E) as L1.
  destruct E as [T [M1 [P [R [Below [Mem1 [F1 S1]]]]]]].
  assert (Dec1 : decode code (pc s1) = Some (Move (S n) 9)) by now rewrite P.
  pose proof (execution_one code s1 (Move (S n) 9) M1 Dec1) as Last.
  exists (execute code s1 (Move (S n) 9)). unfold statement_run.
  split; [eapply steps_trans; eauto |].
  cbn [execute write_reg at_pc mode regs pc mem frontier frames statement_width width].
  rewrite R, put_word. split; [reflexivity |]. split.
  - now apply locals_assignment.
  - repeat split; auto. lia.
Qed.
Lemma emit_write_correct fs code depth env a b m h x m1 h1 y m2 h2 :
  compilation_check fs code = true -> word x = x -> word y = y -> N.to_nat x + 8 <= h2 ->
  expression_compiles fs code depth env a m h x m1 h1 ->
  expression_compiles fs code depth env b m1 h1 y m2 h2 ->
  statement_compiles fs code depth env (Write a b) m h None env (write64 m2 (N.to_nat x) y) h2.
Proof.
  intros C X Y Bound A B s root I M D L Mem F V Layout.
  cbn [valid_statement] in V. apply andb_true_iff in V. destruct V as [Va Vb].
  cbn [emit_statement] in Layout. apply layout_append in Layout. destruct Layout as [La Rest].
  rewrite expression_size in Rest. apply layout_append in Rest. destruct Rest as [Lb End].
  rewrite expression_size in End. cbn [expression_layout] in End. destruct End as [Dec _].
  destruct (emit_pair_correct fs code depth env a b m h x m1 h1 y m2 h2 C A B
    s 9 I M D L Mem F ltac:(lia) Va Vb La Lb) as [s2 E].
  destruct E as [T [M2 [P [R1 [R2 [Below [Mem2 [F2 S2]]]]]]]].
  assert (Dec2 : decode code (pc s2) = Some (Store 9 10)) by now rewrite P.
  pose proof (execution_one code s2 (Store 9 10) M2 Dec2) as Last.
  exists (execute code s2 (Store 9 10)). unfold statement_run.
  split; [eapply steps_trans; eauto |].
  cbn [execute]. rewrite R1, R2, X, Y, F2.
  assert (Check : (N.to_nat x + 8 <=? h2) = true) by now apply Nat.leb_le.
  rewrite Check. cbn [at_pc mode regs pc mem frontier frames statement_width width].
  split; [reflexivity |]. split.
  - intros n N. rewrite Below by lia. now apply L.
  - rewrite Mem2. repeat split; auto. lia.
Qed.
Lemma emit_rewind_correct fs code depth env e m h x m1 h1 :
  word x = x -> N.to_nat x <= h1 ->
  expression_compiles fs code depth env e m h x m1 h1 ->
  statement_compiles fs code depth env (Rewind e) m h None env m1 (N.to_nat x).
Proof.
  intros X Bound A s root I M D L Mem F V Layout.
  cbn [emit_statement] in Layout. apply layout_append in Layout. destruct Layout as [La End].
  rewrite expression_size in End. cbn [expression_layout] in End. destruct End as [Dec _].
  destruct (A s 9 I M D L Mem F ltac:(lia) V La) as [s1 E].
  pose proof (expression_locals env code s e 9 x m1 h1 s1 ltac:(lia) L E) as L1.
  destruct E as [T [M1 [P [R [Below [Mem1 [F1 S1]]]]]]].
  assert (Dec1 : decode code (pc s1) = Some (Reset 9)) by now rewrite P.
  pose proof (execution_one code s1 (Reset 9) M1 Dec1) as Last.
  exists (execute code s1 (Reset 9)). unfold statement_run.
  split; [eapply steps_trans; eauto |].
  cbn [execute]. rewrite R, X, F1.
  assert (Check : (N.to_nat x <=? h1) = true) by now apply Nat.leb_le.
  rewrite Check. cbn [at_pc mode regs pc mem frontier frames statement_width width].
  repeat split; auto. lia.
Qed.
Lemma emit_return_correct fs code depth env e m h x m1 h1 :
  expression_compiles fs code depth env e m h x m1 h1 ->
  statement_compiles fs code depth env (Return e) m h (Some x) env m1 h1.
Proof.
  intros A s root I M D L Mem F V Layout.
  cbn [emit_statement] in Layout. apply layout_append in Layout. destruct Layout as [La End].
  rewrite expression_size in End. cbn [expression_layout width] in End. destruct End as [Dec [Exit _]].
  destruct (A s 9 I M D L Mem F ltac:(lia) V La) as [s1 E].
  pose proof (expression_locals env code s e 9 x m1 h1 s1 ltac:(lia) L E) as L1.
  destruct E as [T [M1 [P [R [Below [Mem1 [F1 S1]]]]]]].
  assert (Dec1 : decode code (pc s1) = Some (Move 0 9)) by now rewrite P.
  pose proof (execution_one code s1 (Move 0 9) M1 Dec1) as Last.
  exists (execute code s1 (Move 0 9)). unfold statement_run.
  split; [eapply steps_trans; eauto |].
  cbn [execute write_reg at_pc mode regs pc mem frontier frames width].
  split; [reflexivity |]. split.
  - intros n N. rewrite put_other by lia. now apply L1.
  - rewrite R, put_same, word_idempotent. repeat split; auto. now rewrite P.
Qed.
Lemma statement_prefix code root inner outer s start t result env m h :
  steps code s start -> frames start = frames s ->
  (result = None -> pc start + statement_width inner = pc s + statement_width outer) ->
  statement_run code root inner start result env m h t ->
  statement_run code root outer s result env m h t.
Proof.
  intros Prefix Frames Size [T [M [L [Mem [F [Stack Exit]]]]]].
  split; [eapply steps_trans; eauto |].
  split; [exact M |]. split; [exact L |]. split; [exact Mem |]. split; [exact F |].
  split; [congruence |]. destruct result; auto. rewrite Exit. now apply Size.
Qed.
Lemma jump_execution code s target : verify code = true -> machine_valid code s -> mode s = Running ->
  decode code (pc s) = Some (Jump target) -> steps code s (at_pc s target).
Proof.
  intros V I M D. pose proof (checked_jump code s target V I D) as G.
  pose proof (execution_one code s (Jump target) M D) as T.
  change (steps code s (transfer code s target)) in T. unfold transfer in T. now rewrite G in T.
Qed.
Lemma branch_execution code s r target : verify code = true -> machine_valid code s -> mode s = Running ->
  decode code (pc s) = Some (Branch r target) ->
  steps code s (at_pc s (if N.eqb (regs s r) 0 then pc s + 10 else target)).
Proof.
  intros V I M D. pose proof (checked_branch code s r target V I D) as G.
  pose proof (execution_one code s (Branch r target) M D) as T.
  change (steps code s (if N.eqb (regs s r) 0 then at_pc s (pc s + 10) else transfer code s target)) in T.
  unfold transfer in T. rewrite G in T. destruct (N.eqb (regs s r) 0); exact T.
Qed.
Definition condition_run code s e v target env m h t :=
  steps code s t /\ mode t = Running /\
  pc t = (if N.eqb v 0 then pc s + expression_width e + 10 else target) /\
  locals_match env (regs t) /\ mem t = m /\ frontier t = h /\ frames t = frames s.
Lemma emit_condition_correct fs code depth env e m h v m1 h1 :
  compilation_check fs code = true -> word v = v ->
  expression_compiles fs code depth env e m h v m1 h1 ->
  forall s target, machine_valid code s -> mode s = Running -> length (frames s) = depth ->
  locals_match env (regs s) -> mem s = m -> frontier s = h -> valid_expression (length fs) e 9 = true ->
  expression_layout code (pc s) (emit_expression (address_of fs) e 9) ->
  decode code (pc s + expression_width e) = Some (Branch 9 target) ->
  exists t, condition_run code s e v target env m1 h1 t.
Proof.
  intros C Word E s target I M D L Mem F V Layout Dec.
  destruct (E s 9 I M D L Mem F ltac:(lia) V Layout) as [s1 Run].
  pose proof (expression_locals env code s e 9 v m1 h1 s1 ltac:(lia) L Run) as L1.
  destruct Run as [T [M1 [P [R [Below [Mem1 [F1 S1]]]]]]].
  pose proof (compilation_verified fs code C) as Verified.
  assert (I1 : machine_valid code s1) by (exact (machine_valid_steps code s s1 Verified I T)).
  assert (Dec1 : decode code (pc s1) = Some (Branch 9 target)) by now rewrite P.
  pose proof (branch_execution code s1 9 target Verified I1 M1 Dec1) as Last.
  rewrite R, Word in Last.
  exists (at_pc s1 (if N.eqb v 0 then pc s1 + 10 else target)). unfold condition_run.
  split; [eapply steps_trans; eauto |].
  cbn [at_pc mode pc regs mem frontier frames]. repeat split; auto. now rewrite P.
Qed.
Lemma emit_sequence_next_correct fs code depth env a b m h env1 m1 h1 result env2 m2 h2 :
  compilation_check fs code = true ->
  statement_compiles fs code depth env a m h None env1 m1 h1 ->
  statement_compiles fs code depth env1 b m1 h1 result env2 m2 h2 ->
  statement_compiles fs code depth env (Sequence a b) m h result env2 m2 h2.
Proof.
  intros C A B s root I M D L Mem F V Layout.
  cbn [valid_statement] in V. apply andb_true_iff in V. destruct V as [Va Vb].
  cbn [emit_statement] in Layout. apply layout_append in Layout. destruct Layout as [La Lb].
  rewrite statement_size in Lb.
  destruct (A s root I M D L Mem F Va La) as [s1 E1].
  destruct E1 as [T1 [M1 [L1 [Mem1 [F1 [S1 P1]]]]]].
  assert (I1 : machine_valid code s1) by (exact (machine_valid_steps code s s1 (compilation_verified fs code C) I T1)).
  assert (D1 : length (frames s1) = depth) by congruence.
  assert (Layout1 : expression_layout code (pc s1) (emit_statement (address_of fs) root b (pc s1))) by now rewrite P1.
  destruct (B s1 root I1 M1 D1 L1 Mem1 F1 Vb Layout1) as [s2 E2].
  exists s2. eapply statement_prefix; [exact T1 | exact S1 | | exact E2].
  intros _. cbn [statement_width]. lia.
Qed.
Lemma emit_sequence_return_correct fs code depth env a b m h x env1 m1 h1 :
  statement_compiles fs code depth env a m h (Some x) env1 m1 h1 ->
  statement_compiles fs code depth env (Sequence a b) m h (Some x) env1 m1 h1.
Proof.
  intros A s root I M D L Mem F V Layout.
  cbn [valid_statement] in V. apply andb_true_iff in V. destruct V as [Va Vb].
  cbn [emit_statement] in Layout. apply layout_append in Layout. destruct Layout as [La _].
  exact (A s root I M D L Mem F Va La).
Qed.
Lemma conditional_layout code address root e yes no p :
  expression_layout code p (emit_statement address root (Conditional e yes no) p) ->
  let no_pc := p + expression_width e + 10 in
  let yes_pc := no_pc + statement_width no + 9 in
  let end_pc := p + statement_width (Conditional e yes no) in
  expression_layout code p (emit_expression address e 9) /\
  decode code (p + expression_width e) = Some (Branch 9 yes_pc) /\
  expression_layout code no_pc (emit_statement address root no no_pc) /\
  decode code (no_pc + statement_width no) = Some (Jump end_pc) /\
  expression_layout code yes_pc (emit_statement address root yes yes_pc).
Proof.
  cbn [emit_statement]. rewrite layout_append. intros [E Rest]. rewrite expression_size in Rest.
  change (decode code (p + expression_width e) =
            Some (Branch 9 (p + expression_width e + 10 + statement_width no + 9)) /\
          expression_layout code (p + expression_width e + 10)
            (emit_statement address root no (p + expression_width e + 10) ++
             [Jump (p + statement_width (Conditional e yes no))] ++
             emit_statement address root yes (p + expression_width e + 10 + statement_width no + 9))) in Rest.
  destruct Rest as [B Rest]. apply layout_append in Rest. destruct Rest as [No Rest].
  rewrite statement_size in Rest. cbn [expression_layout width] in Rest. destruct Rest as [J Yes].
  repeat split; auto.
Qed.
Lemma while_layout code address root e body p :
  expression_layout code p (emit_statement address root (While e body) p) ->
  let body_pc := p + expression_width e + 19 in
  let end_pc := p + statement_width (While e body) in
  expression_layout code p (emit_expression address e 9) /\
  decode code (p + expression_width e) = Some (Branch 9 body_pc) /\
  decode code (p + expression_width e + 10) = Some (Jump end_pc) /\
  expression_layout code body_pc (emit_statement address root body body_pc) /\
  decode code (body_pc + statement_width body) = Some (Jump p).
Proof.
  cbn [emit_statement]. rewrite layout_append. intros [E Rest]. rewrite expression_size in Rest.
  change (decode code (p + expression_width e) = Some (Branch 9 (p + expression_width e + 19)) /\
          decode code (p + expression_width e + 10) = Some (Jump (p + statement_width (While e body))) /\
          expression_layout code (p + expression_width e + 10 + 9)
            (emit_statement address root body (p + expression_width e + 19) ++ [Jump p])) in Rest.
  destruct Rest as [B [J Rest]].
  replace (p + expression_width e + 10 + 9) with (p + expression_width e + 19) in Rest by lia.
  apply layout_append in Rest. destruct Rest as [Body Last]. rewrite statement_size in Last.
  cbn [expression_layout] in Last. destruct Last as [Back _]. repeat split; auto.
Qed.
Lemma emit_conditional_correct fs code depth env e yes no m h v m1 h1 result env2 m2 h2 :
  compilation_check fs code = true -> word v = v ->
  expression_compiles fs code depth env e m h v m1 h1 ->
  statement_compiles fs code depth env (if N.eqb v 0 then no else yes) m1 h1 result env2 m2 h2 ->
  statement_compiles fs code depth env (Conditional e yes no) m h result env2 m2 h2.
Proof.
  intros C Word Test Body s root I M D L Mem F V Layout.
  pose proof (compilation_verified fs code C) as Verified.
  cbn [valid_statement] in V. rewrite !andb_true_iff in V. destruct V as [[Ve Vy] Vn].
  destruct (conditional_layout code (address_of fs) root e yes no (pc s) Layout)
    as [Le [DecBranch [NoLayout [DecJump YesLayout]]]].
  destruct (emit_condition_correct fs code depth env e m h v m1 h1 C Word Test
    s _ I M D L Mem F Ve Le DecBranch) as [s1 E1].
  destruct E1 as [T1 [M1 [P1 [L1 [Mem1 [F1 S1]]]]]].
  assert (I1 : machine_valid code s1) by (exact (machine_valid_steps code s s1 Verified I T1)).
  assert (D1 : length (frames s1) = depth) by congruence.
  destruct (N.eqb v 0) eqn:Choice.
  -
    assert (Layout1 : expression_layout code (pc s1) (emit_statement (address_of fs) root no (pc s1))) by now rewrite P1.
    destruct (Body s1 root I1 M1 D1 L1 Mem1 F1 Vn Layout1) as [s2 E2].
    destruct result as [value|].
    + exists s2. eapply statement_prefix; [exact T1 | exact S1 | | exact E2]. discriminate.
    + destruct E2 as [T2 [M2 [L2 [Mem2 [F2 [S2 P2]]]]]].
      pose proof (steps_trans code s s1 s2 T1 T2) as Prefix.
      assert (I2 : machine_valid code s2) by (exact (machine_valid_steps code s s2 Verified I Prefix)).
      assert (DJ : decode code (pc s2) = Some (Jump (pc s + statement_width (Conditional e yes no)))) by now rewrite P2, P1.
      pose proof (jump_execution code s2 _ Verified I2 M2 DJ) as Last.
      exists (at_pc s2 (pc s + statement_width (Conditional e yes no))). unfold statement_run.
      split; [eapply steps_trans; eauto |].
      cbn [at_pc mode regs pc mem frontier frames]. repeat split; auto. congruence.
  -
    assert (Layout1 : expression_layout code (pc s1) (emit_statement (address_of fs) root yes (pc s1))) by now rewrite P1.
    destruct (Body s1 root I1 M1 D1 L1 Mem1 F1 Vy Layout1) as [s2 E2].
    exists s2. eapply statement_prefix; [exact T1 | exact S1 | | exact E2].
    intros _. rewrite P1. cbn [statement_width]. lia.
Qed.
Lemma emit_while_done_correct fs code depth env e body m h m1 h1 :
  compilation_check fs code = true -> expression_compiles fs code depth env e m h 0%N m1 h1 ->
  statement_compiles fs code depth env (While e body) m h None env m1 h1.
Proof.
  intros C Test s root I M D L Mem F V Layout.
  pose proof (compilation_verified fs code C) as Verified.
  cbn [valid_statement] in V. apply andb_true_iff in V. destruct V as [Ve Vbody].
  destruct (while_layout code (address_of fs) root e body (pc s) Layout) as [Le [DecBranch [DecJump [BodyLayout Back]]]].
  destruct (emit_condition_correct fs code depth env e m h 0%N m1 h1 C eq_refl Test
    s _ I M D L Mem F Ve Le DecBranch) as [s1 E1].
  destruct E1 as [T1 [M1 [P1 [L1 [Mem1 [F1 S1]]]]]].
  cbn in P1.
  assert (I1 : machine_valid code s1) by (exact (machine_valid_steps code s s1 Verified I T1)).
  assert (DJ : decode code (pc s1) = Some (Jump (pc s + statement_width (While e body)))) by now rewrite P1.
  pose proof (jump_execution code s1 _ Verified I1 M1 DJ) as Last.
  exists (at_pc s1 (pc s + statement_width (While e body))). unfold statement_run.
  split; [eapply steps_trans; eauto |]. cbn [at_pc mode pc regs mem frontier frames]. repeat split; auto.
Qed.
Lemma emit_while_return_correct fs code depth env e body m h x m1 h1 value env1 m2 h2 :
  compilation_check fs code = true -> word x = x -> x <> 0%N ->
  expression_compiles fs code depth env e m h x m1 h1 ->
  statement_compiles fs code depth env body m1 h1 (Some value) env1 m2 h2 ->
  statement_compiles fs code depth env (While e body) m h (Some value) env1 m2 h2.
Proof.
  intros C Word Nonzero Test Body s root I M D L Mem F V Layout.
  pose proof (compilation_verified fs code C) as Verified.
  cbn [valid_statement] in V. apply andb_true_iff in V. destruct V as [Ve Vbody].
  destruct (while_layout code (address_of fs) root e body (pc s) Layout) as [Le [DecBranch [_ [BodyLayout _]]]].
  destruct (emit_condition_correct fs code depth env e m h x m1 h1 C Word Test
    s _ I M D L Mem F Ve Le DecBranch) as [s1 E1].
  destruct E1 as [T1 [M1 [P1 [L1 [Mem1 [F1 S1]]]]]].
  apply N.eqb_neq in Nonzero. rewrite Nonzero in P1.
  assert (I1 : machine_valid code s1) by (exact (machine_valid_steps code s s1 Verified I T1)).
  assert (D1 : length (frames s1) = depth) by congruence.
  assert (Layout1 : expression_layout code (pc s1) (emit_statement (address_of fs) root body (pc s1))) by now rewrite P1.
  destruct (Body s1 root I1 M1 D1 L1 Mem1 F1 Vbody Layout1) as [s2 E2].
  exists s2. eapply statement_prefix; [exact T1 | exact S1 | | exact E2]. discriminate.
Qed.
Lemma emit_while_next_correct fs code depth env e body m h x m1 h1 env1 m2 h2 result env2 m3 h3 :
  compilation_check fs code = true -> word x = x -> x <> 0%N ->
  expression_compiles fs code depth env e m h x m1 h1 ->
  statement_compiles fs code depth env body m1 h1 None env1 m2 h2 ->
  statement_compiles fs code depth env1 (While e body) m2 h2 result env2 m3 h3 ->
  statement_compiles fs code depth env (While e body) m h result env2 m3 h3.
Proof.
  intros C Word Nonzero Test Body Loop s root I M D L Mem F V Layout.
  pose proof (compilation_verified fs code C) as Verified.
  pose proof V as WholeValid.
  cbn [valid_statement] in V. apply andb_true_iff in V. destruct V as [Ve Vbody].
  destruct (while_layout code (address_of fs) root e body (pc s) Layout) as [Le [DecBranch [_ [BodyLayout Back]]]].
  destruct (emit_condition_correct fs code depth env e m h x m1 h1 C Word Test
    s _ I M D L Mem F Ve Le DecBranch) as [s1 E1].
  destruct E1 as [T1 [M1 [P1 [L1 [Mem1 [F1 S1]]]]]].
  apply N.eqb_neq in Nonzero. rewrite Nonzero in P1.
  assert (I1 : machine_valid code s1) by (exact (machine_valid_steps code s s1 Verified I T1)).
  assert (D1 : length (frames s1) = depth) by congruence.
  assert (Layout1 : expression_layout code (pc s1) (emit_statement (address_of fs) root body (pc s1))) by now rewrite P1.
  destruct (Body s1 root I1 M1 D1 L1 Mem1 F1 Vbody Layout1) as [s2 E2].
  destruct E2 as [T2 [M2 [L2 [Mem2 [F2 [S2 P2]]]]]].
  pose proof (steps_trans code s s1 s2 T1 T2) as T02.
  assert (I2 : machine_valid code s2) by (exact (machine_valid_steps code s s2 Verified I T02)).
  assert (DB : decode code (pc s2) = Some (Jump (pc s))) by now rewrite P2, P1.
  pose proof (jump_execution code s2 (pc s) Verified I2 M2 DB) as T23.
  set (s3 := at_pc s2 (pc s)).
  pose proof (steps_trans code s s2 s3 T02 T23) as T03.
  assert (I3 : machine_valid code s3) by (exact (machine_valid_steps code s s3 Verified I T03)).
  assert (D3 : length (frames s3) = depth) by (cbn [s3 at_pc frames]; congruence).
  destruct (Loop s3 root I3 eq_refl D3 L2 Mem2 F2 WholeValid Layout) as [s4 E4].
  exists s4. eapply statement_prefix; [exact T03 | | | exact E4].
  - cbn [s3 at_pc frames]. congruence.
  - intros _. reflexivity.
Qed.
Lemma emit_if_yes_correct fs code depth env e yes no m h x m1 h1 result env2 m2 h2 :
  compilation_check fs code = true -> word x = x -> x <> 0%N ->
  expression_compiles fs code depth env e m h x m1 h1 ->
  statement_compiles fs code depth env yes m1 h1 result env2 m2 h2 ->
  statement_compiles fs code depth env (Conditional e yes no) m h result env2 m2 h2.
Proof.
  intros C W N E S. eapply emit_conditional_correct; eauto.
  apply N.eqb_neq in N. now rewrite N.
Qed.
Lemma emit_if_no_correct fs code depth env e yes no m h m1 h1 result env2 m2 h2 :
  compilation_check fs code = true ->
  expression_compiles fs code depth env e m h 0%N m1 h1 ->
  statement_compiles fs code depth env no m1 h1 result env2 m2 h2 ->
  statement_compiles fs code depth env (Conditional e yes no) m h result env2 m2 h2.
Proof.
  intros C E S. eapply emit_conditional_correct; eauto. reflexivity.
Qed.
Lemma emit_discard_correct fs code depth env e m h x m1 h1 :
  expression_compiles fs code depth env e m h x m1 h1 ->
  statement_compiles fs code depth env (Discard e) m h None env m1 h1.
Proof.
  intros A s root I M D L Mem F V Layout.
  destruct (A s 9 I M D L Mem F ltac:(lia) V Layout) as [t Run].
  pose proof (expression_locals env code s e 9 x m1 h1 t ltac:(lia) L Run) as Lt.
  destruct Run as [T [Mt [P [R [Below [Memt [Ft St]]]]]]].
  exists t. unfold statement_run. repeat split; auto.
Qed.
Theorem compiler_execution_correct fs code : compilation_check fs code = true ->
  (forall depth env e m h v m' h', evaluates_expression (source_lookup fs) depth env e m h v m' h' ->
    expression_compiles fs code depth env e m h v m' h') /\
  (forall depth env body m h result env' m' h', evaluates_statement (source_lookup fs) depth env body m h result env' m' h' ->
    statement_compiles fs code depth env body m h result env' m' h').
Proof.
  intro C. apply evaluation_ind; intros depth env.
  - intros n m h. apply emit_literal_correct.
  - intros n m h. apply emit_local_correct.
  - intros op a b m h x m1 h1 y m2 h2 z E1 IH1 E2 IH2 Z.
    eapply emit_operation_correct with (x := x) (y := y); eauto using expression_eval_word.
  - intros op a b m h x m1 h1 y m2 h2 E1 IH1 E2 IH2.
    eapply emit_comparison_correct with (x := x) (y := y); eauto using expression_eval_word.
  - intros a m h x m1 h1 E IH Bound. eapply emit_read_correct with (x := x); eauto using expression_eval_word.
  - intros a m h x m1 h1 E IH Bound. eapply emit_new_correct with (x := x); eauto using expression_eval_word.
  - intros m h. apply emit_watermark_correct.
  - intros f a body m h x m1 h1 result env2 m2 h2 E IH Lookup Nonroot Capacity S IHS.
    eapply emit_invoke_correct with (x := x); eauto using expression_eval_word.
  - intros m h. apply emit_skip_correct.
  - intros n e m h x m1 h1 E IH. now apply emit_assign_correct.
  - intros e m h x m1 h1 E IH. now apply emit_discard_correct with (x := x).
  - intros a b m h x m1 h1 y m2 h2 E1 IH1 E2 IH2 Bound.
    eapply emit_write_correct with (x := x) (y := y); eauto using expression_eval_word.
  - intros e m h x m1 h1 E IH Bound. eapply emit_rewind_correct with (x := x); eauto using expression_eval_word.
  - intros a b m h env1 m1 h1 result env2 m2 h2 E1 IH1 E2 IH2.
    eapply emit_sequence_next_correct; eauto.
  - intros a b m h x env1 m1 h1 E IH. now apply emit_sequence_return_correct.
  - intros e a b m h x m1 h1 result env2 m2 h2 E IH Nonzero S IHS.
    eapply emit_if_yes_correct with (x := x); eauto using expression_eval_word.
  - intros e a b m h m1 h1 result env2 m2 h2 E IH S IHS.
    eapply emit_if_no_correct; eauto.
  - intros e body m h m1 h1 E IH. eapply emit_while_done_correct; eauto.
  - intros e body m h x m1 h1 env1 m2 h2 result env2 m3 h3 E IH Nonzero S IHS Loop IHLoop.
    eapply emit_while_next_correct with (x := x); eauto using expression_eval_word.
  - intros e body m h x m1 h1 result env1 m2 h2 E IH Nonzero S IHS.
    eapply emit_while_return_correct with (x := x); eauto using expression_eval_word.
  - intros e m h x m1 h1 E IH. now apply emit_return_correct.
Qed.
Theorem compiled_program_terminates fs code main value env m h :
  compilation_check fs code = true -> nth_error fs 0 = Some main ->
  evaluates_statement (source_lookup fs) 0 (fun _ => 0%N) main (fun _ => 0%N) 0 (Some value) env m h ->
  exists t, steps code initial t /\ mode t = Stopped /\ regs t 0 = value /\ mem t = m /\ frontier t = h.
Proof.
  intros C Main E. pose proof (compilation_verified fs code C) as V.
  destruct (checked_function fs code 0 main C Main) as [Valid [Layout Address]].
  cbn [Nat.eqb] in Layout, Address. rewrite Address in Layout.
  apply layout_append in Layout. destruct Layout as [Header BodyLayout].
  rewrite prologue_size in BodyLayout. cbn [prologue_width] in BodyLayout.
  cbn [prologue expression_layout] in Header. destruct Header as [EntryDecode _].
  pose proof (execution_one code initial Entry eq_refl EntryDecode) as T01.
  set (s1 := execute code initial Entry).
  assert (I0 : machine_valid code initial).
  { split; [apply initial_well_formed |]. split; [apply initial_canonical | now apply accepted_initial]. }
  assert (I1 : machine_valid code s1) by (exact (machine_valid_steps code initial s1 V I0 T01)).
  assert (Locals : locals_match (fun _ => 0%N) (regs s1)) by (intros n N; reflexivity).
  destruct (proj2 (compiler_execution_correct fs code C) _ _ _ _ _ _ _ _ _ E
    s1 true I1 eq_refl eq_refl Locals eq_refl eq_refl Valid BodyLayout) as [s2 Run].
  destruct Run as [T12 [M2 [L2 [Mem2 [F2 [S2 [R2 HaltDecode]]]]]]].
  pose proof (steps_trans code initial s1 s2 T01 T12) as Prefix.
  pose proof (execution_one code s2 Halt M2 HaltDecode) as Last.
  exists (finish s2 Stopped). split; [eapply steps_trans; eauto |].
  cbn [finish mode regs mem frontier]. repeat split; auto.
  rewrite R2. exact (proj2 (evaluations_canonical (source_lookup fs)) _ _ _ _ _ _ _ _ _ E value eq_refl).
Qed.
Inductive normal_execution fs : source_state -> source_state -> Prop :=
| normal_main main value env m h : nth_error fs 0 = Some main ->
    evaluates_statement (source_lookup fs) 0 (fun _ => 0%N) main (fun _ => 0%N) 0 (Some value) env m h ->
    normal_execution fs (source_initial main) (SourceState (Value value) env m h 0 [] Stopped).
Inductive compilation_matches fs : source_state -> state -> Prop :=
| compilation_entry main : nth_error fs 0 = Some main -> compilation_matches fs (source_initial main) initial
| compilation_result value env m h t :
    mode t = Stopped -> regs t 0 = value -> mem t = m -> frontier t = h ->
    compilation_matches fs (SourceState (Value value) env m h 0 [] Stopped) t.
Record forward_simulation (source_relation : source_state -> source_state -> Prop) (code : list nat)
       (matches : source_state -> state -> Prop) := {
  simulate_step : forall s s' t, matches s t -> source_relation s s' ->
    exists t', steps code t t' /\ matches s' t';
  simulate_result : forall s t, matches s t -> source_mode s = Stopped ->
    exists v, source_control s = Value v /\ mode t = Stopped /\ regs t 0 = v
}.
Inductive source_closure (relation : source_state -> source_state -> Prop) : source_state -> source_state -> Prop :=
| closure_refl s : source_closure relation s s
| closure_step s t u : relation s t -> source_closure relation t u -> source_closure relation s u.
Theorem forward_simulation_execution relation code matches :
  forward_simulation relation code matches ->
  forall s s' t, source_closure relation s s' -> matches s t ->
  exists t', steps code t t' /\ matches s' t'.
Proof.
  intros F s s' t H. revert t. induction H; intros t0 M.
  - exists t0. split; [constructor | assumption].
  - destruct (simulate_step _ _ _ F _ _ _ M H) as [t1 [T M1]].
    destruct (IHsource_closure _ M1) as [t2 [T2 M2]].
    exists t2. split; eauto using steps_trans.
Qed.
Theorem compiled_normal_execution_simulation fs code : compilation_check fs code = true ->
  forward_simulation (normal_execution fs) code (compilation_matches fs).
Proof.
  intro C. constructor.
  - intros s s' t Match Run.
    inversion Run as [main value env m h Lookup Eval]; subst.
    inversion Match; subst.
    destruct (compiled_program_terminates fs code main value env m h C Lookup Eval) as [u [T [M [R [Mem F]]]]].
    exists u. split; auto. now apply compilation_result.
  - intros s t Match StoppedMode. inversion Match; subst; cbn [source_initial source_mode] in StoppedMode; try discriminate.
    exists (regs t 0). repeat split; auto.
Qed.
Theorem compiler_initial_match fs code : compilation_check fs code = true ->
  exists main, compilation_matches fs (source_initial main) initial.
Proof.
  intro C. destruct (compilation_main fs code C) as [main Main].
  exists main. now constructor.
Qed.
