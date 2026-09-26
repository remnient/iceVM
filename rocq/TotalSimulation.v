From Stdlib Require Import List NArith Arith Bool Lia.
From Loosevm Require Import Syntax State Semantics Interpreter Verifier Source Compiler Encoding Frontend Simulation Optimisation.
Import ListNotations.
Local Opaque memory_size stack_size.
Definition ready code depth env m h s :=
  machine_valid code s /\ mode s = Running /\ length (frames s) = depth /\
  locals_match env (regs s) /\ mem s = m /\ frontier s = h.
Definition matches_configuration fs code c s :=
  match c with
  | Expression depth env e m h => exists d, ready code depth env m h s /\ 9 <= d /\
      valid_expression (length fs) e d = true /\
      expression_layout code (pc s) (emit_expression (address_of fs) e d)
  | Statement depth env body m h => exists root, ready code depth env m h s /\
      valid_statement (length fs) body = true /\
      expression_layout code (pc s) (emit_statement (address_of fs) root body (pc s))
  end.
Definition positive_steps code s t := exists u, transition code s u /\ steps code u t.
Lemma different_positive code s t : steps code s t -> s <> t -> positive_steps code s t.
Proof. intros T N. inversion T; subst; [contradiction | eexists; eauto]. Qed.
Lemma positive_trans code s t u : positive_steps code s t -> steps code t u -> positive_steps code s u.
Proof. intros [a [A B]] C. exists a. split; auto. eauto using steps_trans. Qed.
Lemma expression_ready code depth env e s d v m h t :
  verify code = true -> ready code depth env (mem s) (frontier s) s -> 9 <= d ->
  expression_run code s e d v m h t -> ready code depth env m h t.
Proof.
  intros V [I [M [D [L _]]]] B Run.
  pose proof (expression_locals env code s e d v m h t B L Run) as Lt.
  destruct Run as [T [Mt [P [R [Below [Mem [F Stack]]]]]]].
  unfold ready. split; [exact (machine_valid_steps code s t V I T) |].
  repeat split; auto; congruence.
Qed.
Lemma statement_ready code depth env root body s result env1 m h t :
  verify code = true -> ready code depth env (mem s) (frontier s) s ->
  statement_run code root body s result env1 m h t -> ready code depth env1 m h t.
Proof.
  intros V [I [M [D [L _]]]] [T [Mt [Lt [Mem [F [Stack Exit]]]]]].
  unfold ready. split; [exact (machine_valid_steps code s t V I T) |].
  repeat split; auto; congruence.
Qed.
Lemma ready_self code depth env m h s : ready code depth env m h s ->
  ready code depth env (mem s) (frontier s) s.
Proof. unfold ready. tauto. Qed.
Lemma normal_expression fs code depth env e m h x m1 h1 s d :
  compilation_check fs code = true ->
  evaluates_expression (source_lookup fs) depth env e m h x m1 h1 ->
  ready code depth env m h s -> 9 <= d -> valid_expression (length fs) e d = true ->
  expression_layout code (pc s) (emit_expression (address_of fs) e d) ->
  exists t, expression_run code s e d x m1 h1 t /\ ready code depth env m1 h1 t.
Proof.
  intros C E R B V Layout. destruct R as [I [M [D [L [Mem F]]]]].
  destruct (proj1 (compiler_execution_correct fs code C) _ _ _ _ _ _ _ _ E
    s d I M D L Mem F B V Layout) as [t Run].
  exists t. split; auto. eapply expression_ready; eauto using compilation_verified.
  unfold ready. tauto.
Qed.
Lemma normal_statement fs code depth env body m h result env1 m1 h1 s root :
  compilation_check fs code = true ->
  evaluates_statement (source_lookup fs) depth env body m h result env1 m1 h1 ->
  ready code depth env m h s -> valid_statement (length fs) body = true ->
  expression_layout code (pc s) (emit_statement (address_of fs) root body (pc s)) ->
  exists t, statement_run code root body s result env1 m1 h1 t /\ ready code depth env1 m1 h1 t.
Proof.
  intros C E R V Layout. destruct R as [I [M [D [L [Mem F]]]]].
  destruct (proj2 (compiler_execution_correct fs code C) _ _ _ _ _ _ _ _ _ E
    s root I M D L Mem F V Layout) as [t Run].
  exists t. split; auto. apply (statement_ready code depth env root body s result env1 m1 h1 t
    (compilation_verified fs code C)); auto. unfold ready. tauto.
Qed.
Lemma expression_width_positive e : 0 < expression_width e.
Proof. induction e; cbn; lia. Qed.
Lemma expression_positive code s e d v m h t :
  expression_run code s e d v m h t -> positive_steps code s t.
Proof.
  intros [T [_ [P _]]]. apply different_positive; auto.
  intro E. subst t. pose proof (expression_width_positive e). lia.
Qed.
Lemma ready_at code depth env m h s p : verify code = true -> ready code depth env m h s ->
  steps code s (at_pc s p) -> ready code depth env m h (at_pc s p).
Proof.
  intros V [I [M [D [L [Mem F]]]]] T. unfold ready.
  split; [exact (machine_valid_steps code s (at_pc s p) V I T) |]. auto.
Qed.
Lemma call_entry fs code depth env f a body m h x m1 h1 s :
  compilation_check fs code = true ->
  evaluates_expression (source_lookup fs) depth env a m h x m1 h1 ->
  nth_error fs f = Some body -> f <> 0 -> depth < stack_size ->
  matches_configuration fs code (Expression depth env (Invoke f a) m h) s ->
  exists t, positive_steps code s t /\ steps code s t /\
    matches_configuration fs code (Statement (S depth) (put (fun _ => 0%N) 0 x) body m1 h1) t.
Proof.
  intros C Eval Lookup Nonroot Capacity [d [R [Bound [V Layout]]]].
  destruct R as [I [M [D [L [Mem F]]]]].
  pose proof (compilation_verified fs code C) as Verified.
  cbn [valid_expression] in V. rewrite !andb_true_iff in V. destruct V as [_ [[_ _] Va]].
  cbn [emit_expression] in Layout. apply layout_append in Layout. destruct Layout as [La Tail].
  rewrite expression_size in Tail. cbn [expression_layout width] in Tail.
  destruct Tail as [DecArg [DecCall [DecOut _]]].
  destruct (normal_expression fs code depth env a m h x m1 h1 s d C Eval
    ltac:(unfold ready; tauto) Bound Va La) as [s1 [Run1 Ready1]].
  pose proof (expression_positive code s a d x m1 h1 s1 Run1) as Positive.
  destruct Run1 as [T1 [M1 [P1 [R1 [Below1 [Mem1 [F1 S1]]]]]]].
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
  exists s4. split.
  - eapply positive_trans; [exact Positive |]. eauto using steps_trans.
  - split; auto. exists false. split.
    + unfold ready. split; [exact (machine_valid_steps code s s4 Verified I T4) |].
      split; auto. split.
      * rewrite S4. cbn [s3 frames length]. rewrite S2, S1, D. reflexivity.
      * split; auto.
    + split; auto. rewrite P4. exact BodyLayout.
Qed.
Theorem descends_simulation fs code parent child :
  compilation_check fs code = true -> descends (source_lookup fs) parent child ->
  forall s, matches_configuration fs code parent s ->
  exists t, steps code s t /\ matches_configuration fs code child t /\
    (configuration_rank child < configuration_rank parent \/ positive_steps code s t).
Proof.
  intros C Des. pose proof (compilation_verified fs code C) as Verified.
  destruct Des; intros s Match.
  - destruct Match as [r [R [Bound [V Layout]]]].
    cbn [valid_expression] in V. rewrite !andb_true_iff in V. destruct V as [_ [Va Vb]].
    cbn [emit_expression] in Layout. apply layout_append in Layout. destruct Layout as [La _].
    exists s. split; [constructor |]. split; [exists r; auto | left; cbn; lia].
  - destruct Match as [r [R [Bound [V Layout]]]].
    cbn [valid_expression] in V. rewrite !andb_true_iff in V. destruct V as [_ [Va Vb]].
    cbn [emit_expression] in Layout. apply layout_append in Layout. destruct Layout as [La Tail].
    rewrite expression_size in Tail. apply layout_append in Tail. destruct Tail as [Lb _].
    destruct (normal_expression fs code d env a m h x m1 h1 s r C H R Bound Va La) as [t [Run Rt]].
    destruct Run as [T [_ [P _]]]. exists t. split; auto. split.
    + exists (S r). split; auto. split; [lia |]. split; auto. now rewrite P.
    + left. cbn. lia.
  - destruct Match as [r [R [Bound [V Layout]]]].
    cbn [valid_expression] in V. rewrite !andb_true_iff in V. destruct V as [_ [Va Vb]].
    cbn [emit_expression] in Layout. apply layout_append in Layout. destruct Layout as [La _].
    exists s. split; [constructor |]. split; [exists r; auto | left; cbn; lia].
  - destruct Match as [r [R [Bound [V Layout]]]].
    cbn [valid_expression] in V. rewrite !andb_true_iff in V. destruct V as [_ [Va Vb]].
    cbn [emit_expression] in Layout. apply layout_append in Layout. destruct Layout as [La Tail].
    rewrite expression_size in Tail. apply layout_append in Tail. destruct Tail as [Lb _].
    destruct (normal_expression fs code d env a m h x m1 h1 s r C H R Bound Va La) as [t [Run Rt]].
    destruct Run as [T [_ [P _]]]. exists t. split; auto. split.
    + exists (S r). split; auto. split; [lia |]. split; auto. now rewrite P.
    + left. cbn. lia.
  - destruct Match as [r [R [Bound [V Layout]]]].
    cbn [valid_expression] in V. apply andb_true_iff in V. destruct V as [_ Va].
    cbn [emit_expression] in Layout. apply layout_append in Layout. destruct Layout as [La _].
    exists s. split; [constructor |]. split; [exists r; auto | left; cbn; lia].
  - destruct Match as [r [R [Bound [V Layout]]]].
    cbn [valid_expression] in V. apply andb_true_iff in V. destruct V as [_ Va].
    cbn [emit_expression] in Layout. apply layout_append in Layout. destruct Layout as [La _].
    exists s. split; [constructor |]. split; [exists r; auto | left; cbn; lia].
  - destruct Match as [r [R [Bound [V Layout]]]].
    cbn [valid_expression] in V. rewrite !andb_true_iff in V. destruct V as [_ [[_ _] Va]].
    cbn [emit_expression] in Layout. apply layout_append in Layout. destruct Layout as [La _].
    exists s. split; [constructor |]. split; [exists r; auto | left; cbn; lia].
  - destruct (call_entry fs code d env f a body m h x m1 h1 s C H H0 H1 H2 Match)
      as [t [Pos [T Mt]]]. exists t. auto.
  - destruct Match as [root [R [V Layout]]].
    cbn [valid_statement] in V. apply andb_true_iff in V. destruct V as [_ Ve].
    cbn [emit_statement] in Layout. apply layout_append in Layout. destruct Layout as [Le _].
    exists s. split; [constructor |]. split; [exists 9; auto | left; cbn; lia].
  - destruct Match as [root [R [V Layout]]].
    exists s. split; [constructor |]. split; [exists 9; auto | left; cbn; lia].
  - destruct Match as [root [R [V Layout]]].
    cbn [valid_statement] in V. apply andb_true_iff in V. destruct V as [Va Vb].
    cbn [emit_statement] in Layout. apply layout_append in Layout. destruct Layout as [La _].
    exists s. split; [constructor |]. split; [exists 9; auto | left; cbn; lia].
  - destruct Match as [root [R [V Layout]]].
    cbn [valid_statement] in V. apply andb_true_iff in V. destruct V as [Va Vb].
    cbn [emit_statement] in Layout. apply layout_append in Layout. destruct Layout as [La Tail].
    rewrite expression_size in Tail. apply layout_append in Tail. destruct Tail as [Lb _].
    destruct (normal_expression fs code d env a m h x m1 h1 s 9 C H R ltac:(lia) Va La) as [t [Run Rt]].
    destruct Run as [T [_ [P _]]]. exists t. split; auto. split.
    + exists 10. split; auto. split; [lia |]. split; auto. now rewrite P.
    + left. cbn. lia.
  - destruct Match as [root [R [V Layout]]].
    cbn [emit_statement] in Layout. apply layout_append in Layout. destruct Layout as [Le _].
    exists s. split; [constructor |]. split; [exists 9; auto | left; cbn; lia].
  - destruct Match as [root [R [V Layout]]].
    cbn [valid_statement] in V. apply andb_true_iff in V. destruct V as [Va Vb].
    cbn [emit_statement] in Layout. apply layout_append in Layout. destruct Layout as [La _].
    exists s. split; [constructor |]. split; [exists root; auto | left; cbn; lia].
  - destruct Match as [root [R [V Layout]]].
    cbn [valid_statement] in V. apply andb_true_iff in V. destruct V as [Va Vb].
    cbn [emit_statement] in Layout. apply layout_append in Layout. destruct Layout as [La Lb].
    rewrite statement_size in Lb.
    destruct (normal_statement fs code d env a m h None env1 m1 h1 s root C H R Va La)
      as [t [Run Rt]]. destruct Run as [T [_ [_ [_ [_ [_ P]]]]]].
    exists t. split; auto. split.
    + exists root. split; auto. split; auto. now rewrite P.
    + left. cbn. lia.
  - destruct Match as [root [R [V Layout]]].
    cbn [valid_statement] in V. rewrite !andb_true_iff in V. destruct V as [[Ve Va] Vb].
    destruct (conditional_layout code (address_of fs) root e a b (pc s) Layout) as [Le _].
    exists s. split; [constructor |]. split; [exists 9; auto | left; cbn; lia].
  - destruct Match as [root [R [V Layout]]]. pose proof R as R0.
    destruct R as [I [M [D [L [Mem F]]]]].
    cbn [valid_statement] in V. rewrite !andb_true_iff in V. destruct V as [[Ve Va] Vb].
    destruct (conditional_layout code (address_of fs) root e a b (pc s) Layout)
      as [Le [Branch [No [_ Yes]]]].
    pose proof (expression_eval_word fs d env e m h x m1 h1 H) as Word.
    destruct (emit_condition_correct fs code d env e m h x m1 h1 C Word
      (proj1 (compiler_execution_correct fs code C) _ _ _ _ _ _ _ _ H)
      s _ I M D L Mem F Ve Le Branch) as [t Run].
    destruct Run as [T [Mt [P [Lt [Memt [Ft Stack]]]]]].
    assert (Rt : ready code d env m1 h1 t).
    { unfold ready. split; [exact (machine_valid_steps code s t Verified I T) |]. repeat split; auto; congruence. }
    exists t. split; auto. split.
    + exists root. split; auto. split; destruct (N.eqb x 0); auto; now rewrite P.
    + left. cbn. destruct (N.eqb x 0); cbn; lia.
  - destruct Match as [root [R [V Layout]]].
    cbn [valid_statement] in V. apply andb_true_iff in V. destruct V as [Ve Vb].
    destruct (while_layout code (address_of fs) root e body (pc s) Layout) as [Le _].
    exists s. split; [constructor |]. split; [exists 9; auto | left; cbn; lia].
  - destruct Match as [root [R [V Layout]]].
    destruct R as [I [M [D [L [Mem F]]]]].
    cbn [valid_statement] in V. apply andb_true_iff in V. destruct V as [Ve Vbody].
    destruct (while_layout code (address_of fs) root e body (pc s) Layout) as [Le [Branch [_ [Body _]]]].
    pose proof (expression_eval_word fs d env e m h x m1 h1 H) as Word.
    destruct (emit_condition_correct fs code d env e m h x m1 h1 C Word
      (proj1 (compiler_execution_correct fs code C) _ _ _ _ _ _ _ _ H)
      s _ I M D L Mem F Ve Le Branch) as [t Run].
    destruct Run as [T [Mt [P [Lt [Memt [Ft Stack]]]]]].
    apply N.eqb_neq in H0. rewrite H0 in P.
    exists t. split; auto. split.
    + exists root. split.
      * unfold ready. split; [exact (machine_valid_steps code s t Verified I T) |]. repeat split; auto; congruence.
      * split; auto. now rewrite P.
    + left. cbn. lia.
  - destruct Match as [root [R [V Layout]]]. pose proof V as WholeValid.
    destruct R as [I [M [D [L [Mem F]]]]].
    cbn [valid_statement] in V. apply andb_true_iff in V. destruct V as [Ve Vbody].
    destruct (while_layout code (address_of fs) root e body (pc s) Layout) as [Le [Branch [_ [Body Back]]]].
    pose proof (expression_eval_word fs d env e m h x m1 h1 H) as Word.
    destruct (emit_condition_correct fs code d env e m h x m1 h1 C Word
      (proj1 (compiler_execution_correct fs code C) _ _ _ _ _ _ _ _ H)
      s _ I M D L Mem F Ve Le Branch) as [s1 Run1].
    destruct Run1 as [T1 [M1 [P1 [L1 [Mem1 [F1 S1]]]]]].
    apply N.eqb_neq in H0. rewrite H0 in P1.
    assert (I1 : machine_valid code s1) by (exact (machine_valid_steps code s s1 Verified I T1)).
    assert (D1 : length (frames s1) = d) by congruence.
    assert (Body1 : expression_layout code (pc s1) (emit_statement (address_of fs) root body (pc s1))) by now rewrite P1.
    destruct (normal_statement fs code d env body m1 h1 None env1 m2 h2 s1 root C H1
      ltac:(unfold ready; tauto) Vbody Body1) as [s2 [Run2 R2]].
    destruct Run2 as [T2 [M2 [L2 [Mem2 [F2 [S2 P2]]]]]].
    pose proof (steps_trans code s s1 s2 T1 T2) as T02.
    assert (I2 : machine_valid code s2) by (exact (machine_valid_steps code s s2 Verified I T02)).
    assert (DB : decode code (pc s2) = Some (Jump (pc s))) by now rewrite P2, P1.
    pose proof (jump_execution code s2 (pc s) Verified I2 M2 DB) as T23.
    set (s3 := at_pc s2 (pc s)).
    pose proof (steps_trans code s s2 s3 T02 T23) as T03.
    exists s3. split; auto. split.
    + exists root. split.
      * eapply ready_at; eauto.
      * split; auto.
    + right. apply (positive_trans code s s1 s3).
      * apply different_positive; [exact T1 |]. intro E. subst s1. lia.
      * exact (steps_trans code s1 s2 s3 T2 T23).
  - destruct Match as [root [R [V Layout]]].
    cbn [emit_statement] in Layout. apply layout_append in Layout. destruct Layout as [Le _].
    exists s. split; [constructor |]. split; [exists 9; auto | left; cbn; lia].
Qed.
Definition fault_run code s f m h := exists t,
  steps code s t /\ mode t = Fault f /\ mem t = m /\ frontier t = h.
Lemma fault_prefix code s t f m h : steps code s t -> fault_run code t f m h -> fault_run code s f m h.
Proof. intros T [u [U O]]. exists u. split; eauto using steps_trans. Qed.
Lemma normal_pair fs code depth env a b m h x m1 h1 y m2 h2 s d :
  compilation_check fs code = true ->
  evaluates_expression (source_lookup fs) depth env a m h x m1 h1 ->
  evaluates_expression (source_lookup fs) depth env b m1 h1 y m2 h2 ->
  ready code depth env m h s -> 9 <= d ->
  valid_expression (length fs) a d = true -> valid_expression (length fs) b (S d) = true ->
  expression_layout code (pc s) (emit_expression (address_of fs) a d) ->
  expression_layout code (pc s + expression_width a) (emit_expression (address_of fs) b (S d)) ->
  exists t, pair_run code s a b d x y m2 h2 t.
Proof.
  intros C A B [I [M [D [L [Mem F]]]]] Bound Va Vb La Lb.
  exact (emit_pair_correct fs code depth env a b m h x m1 h1 y m2 h2 C
    (proj1 (compiler_execution_correct fs code C) _ _ _ _ _ _ _ _ A)
    (proj1 (compiler_execution_correct fs code C) _ _ _ _ _ _ _ _ B)
    s d I M D L Mem F Bound Va Vb La Lb).
Qed.
Lemma failed_call code s target : call_target code target = true ->
  local_target code (pc s) (pc s + 9) = true -> stack_size <= length (frames s) ->
  execute code s (Call target) = finish s (Fault Stack).
Proof.
  intros C L S. cbn [execute at_pc pc width]. rewrite C, L. cbn -[Nat.ltb].
  assert (B : (length (frames s) <? stack_size) = false) by now apply Nat.ltb_ge.
  now rewrite B.
Qed.
Theorem local_fault_simulation fs code c f m' h' :
  compilation_check fs code = true -> local_fault (source_lookup fs) c f m' h' ->
  forall s, matches_configuration fs code c s -> fault_run code s f m' h'.
Proof.
  intros C Fault. destruct Fault; intros s Match.
  - destruct Match as [r [R [Bound [V Layout]]]].
    cbn [valid_expression] in V. rewrite !andb_true_iff in V. destruct V as [_ [Va Vb]].
    cbn [emit_expression] in Layout. apply layout_append in Layout. destruct Layout as [La Tail].
    rewrite expression_size in Tail. apply layout_append in Tail. destruct Tail as [Lb End].
    rewrite expression_size in End. cbn [expression_layout] in End. destruct End as [Dec _].
    destruct (normal_pair fs code d env a b m h x m1 h1 y m2 h2 s r C H H0 R Bound Va Vb La Lb)
      as [t [T [M [P [X [Y [_ [Mem [F _]]]]]]]]].
    assert (Dec1 : decode code (pc t) = Some (Binary op r r (S r))) by now rewrite P.
    pose proof (execution_one code t (Binary op r r (S r)) M Dec1) as Last.
    assert (E : execute code t (Binary op r r (S r)) = finish t (Fault Division)).
    { cbn [execute]. rewrite X, Y, (expression_eval_word fs d env a m h x m1 h1 H),
        (expression_eval_word fs d env b m1 h1 y m2 h2 H0), H1. reflexivity. }
    rewrite E in Last. exists (finish t (Fault Division)). split; [eapply steps_trans; eauto |].
    cbn [finish mode mem frontier]. auto.
  - destruct Match as [r [R [Bound [V Layout]]]].
    cbn [valid_expression] in V. apply andb_true_iff in V. destruct V as [_ Va].
    cbn [emit_expression] in Layout. apply layout_append in Layout. destruct Layout as [La End].
    rewrite expression_size in End. cbn [expression_layout] in End. destruct End as [Dec _].
    destruct (normal_expression fs code d env a m h x m1 h1 s r C H R Bound Va La)
      as [t [[T [M [P [X [_ [Mem [F _]]]]]]] Rt]].
    assert (Dec1 : decode code (pc t) = Some (Load r r)) by now rewrite P.
    pose proof (execution_one code t (Load r r) M Dec1) as Last.
    assert (E : execute code t (Load r r) = finish t (Fault Memory)).
    { cbn [execute]. rewrite X, (expression_eval_word fs d env a m h x m1 h1 H), F.
      assert (Check : (N.to_nat x + 8 <=? h1) = false) by now apply Nat.leb_gt.
      now rewrite Check. }
    rewrite E in Last. exists (finish t (Fault Memory)). split; [eapply steps_trans; eauto |].
    cbn [finish mode mem frontier]. auto.
  - destruct Match as [r [R [Bound [V Layout]]]].
    cbn [valid_expression] in V. apply andb_true_iff in V. destruct V as [_ Va].
    cbn [emit_expression] in Layout. apply layout_append in Layout. destruct Layout as [La End].
    rewrite expression_size in End. cbn [expression_layout] in End. destruct End as [Dec _].
    destruct (normal_expression fs code d env a m h x m1 h1 s r C H R Bound Va La)
      as [t [[T [M [P [X [_ [Mem [F _]]]]]]] Rt]].
    assert (Dec1 : decode code (pc t) = Some (Alloc r r)) by now rewrite P.
    pose proof (execution_one code t (Alloc r r) M Dec1) as Last.
    assert (E : execute code t (Alloc r r) = finish t (Fault Memory)).
    { cbn [execute]. rewrite X, (expression_eval_word fs d env a m h x m1 h1 H), F.
      assert (Check : (h1 + N.to_nat x <=? memory_size) = false) by now apply Nat.leb_gt.
      now rewrite Check. }
    rewrite E in Last. exists (finish t (Fault Memory)). split; [eapply steps_trans; eauto |].
    cbn [finish mode mem frontier]. auto.
  - destruct Match as [r [R [Bound [V Layout]]]]. pose proof R as Ready.
    destruct R as [I [M [D [L [Mem F]]]]].
    cbn [valid_expression] in V. rewrite !andb_true_iff in V. destruct V as [_ [[_ _] Va]].
    cbn [emit_expression] in Layout. apply layout_append in Layout. destruct Layout as [La Tail].
    rewrite expression_size in Tail. cbn [expression_layout width] in Tail.
    destruct Tail as [DecArg [DecCall _]].
    destruct (normal_expression fs code d env a m h x m1 h1 s r C H Ready Bound Va La)
      as [s1 [[T1 [M1 [P1 [X [_ [Mem1 [F1 S1]]]]]]] Ready1]].
    set (s2 := execute code s1 (Move 15 r)).
    assert (T12 : steps code s1 s2) by (apply execution_one; auto; now rewrite P1).
    pose proof (steps_trans code s s1 s2 T1 T12) as T2.
    assert (I2 : machine_valid code s2) by (exact (machine_valid_steps code s s2 (compilation_verified fs code C) I T2)).
    assert (Dec2 : decode code (pc s2) = Some (Call (address_of fs f))).
    { cbn [s2 execute write_reg at_pc pc]. now rewrite P1. }
    destruct (checked_call code s2 (address_of fs f) (compilation_verified fs code C) I2 Dec2)
      as [Callable Local].
    pose proof (execution_one code s2 (Call (address_of fs f)) eq_refl Dec2) as Last.
    assert (E : execute code s2 (Call (address_of fs f)) = finish s2 (Fault Stack)).
    { apply failed_call; auto. change (stack_size <= length (frames s1)). now rewrite S1, D. }
    rewrite E in Last. exists (finish s2 (Fault Stack)). split; [eapply steps_trans; eauto |].
    cbn [finish mode mem frontier s2 execute write_reg at_pc]. auto.
  - destruct Match as [root [R [V Layout]]].
    cbn [valid_statement] in V. apply andb_true_iff in V. destruct V as [Va Vb].
    cbn [emit_statement] in Layout. apply layout_append in Layout. destruct Layout as [La Tail].
    rewrite expression_size in Tail. apply layout_append in Tail. destruct Tail as [Lb End].
    rewrite expression_size in End. cbn [expression_layout] in End. destruct End as [Dec _].
    destruct (normal_pair fs code d env a b m h x m1 h1 y m2 h2 s 9 C H H0 R ltac:(lia) Va Vb La Lb)
      as [t [T [M [P [X [Y [_ [Mem [F _]]]]]]]]].
    assert (Dec1 : decode code (pc t) = Some (Store 9 10)) by now rewrite P.
    pose proof (execution_one code t (Store 9 10) M Dec1) as Last.
    assert (E : execute code t (Store 9 10) = finish t (Fault Memory)).
    { cbn [execute]. rewrite X, (expression_eval_word fs d env a m h x m1 h1 H), F.
      assert (Check : (N.to_nat x + 8 <=? h2) = false) by now apply Nat.leb_gt.
      now rewrite Check. }
    rewrite E in Last. exists (finish t (Fault Memory)). split; [eapply steps_trans; eauto |].
    cbn [finish mode mem frontier]. auto.
  - destruct Match as [root [R [V Layout]]].
    cbn [emit_statement] in Layout. apply layout_append in Layout. destruct Layout as [La End].
    rewrite expression_size in End. cbn [expression_layout] in End. destruct End as [Dec _].
    destruct (normal_expression fs code d env e m h x m1 h1 s 9 C H R ltac:(lia) V La)
      as [t [[T [M [P [X [_ [Mem [F _]]]]]]] Rt]].
    assert (Dec1 : decode code (pc t) = Some (Reset 9)) by now rewrite P.
    pose proof (execution_one code t (Reset 9) M Dec1) as Last.
    assert (E : execute code t (Reset 9) = finish t (Fault Region)).
    { cbn [execute]. rewrite X, (expression_eval_word fs d env e m h x m1 h1 H), F.
      assert (Check : (N.to_nat x <=? h1) = false) by now apply Nat.leb_gt.
      now rewrite Check. }
    rewrite E in Last. exists (finish t (Fault Region)). split; [eapply steps_trans; eauto |].
    cbn [finish mode mem frontier]. auto.
Qed.
Theorem compiler_fault_correct fs code c f m h :
  compilation_check fs code = true -> raises (source_lookup fs) c f m h ->
  forall s, matches_configuration fs code c s -> fault_run code s f m h.
Proof.
  intros C E. induction E; intros s Match.
  - eapply local_fault_simulation; eauto.
  - destruct (descends_simulation fs code c child C H s Match) as [t [T [Mt _]]].
    eapply fault_prefix; [exact T | now apply IHE].
Qed.
Theorem compiler_divergence_correct fs code : compilation_check fs code = true ->
  forall c s, source_diverges (source_lookup fs) c -> matches_configuration fs code c s ->
  forall z, steps code s z -> mode z = Running.
Proof.
  intro C.
  assert (NoTerminal : forall n rank c s z, configuration_rank c <= rank ->
    source_diverges (source_lookup fs) c -> matches_configuration fs code c s ->
    counted code n s z -> mode z <> Running -> False).
  {
    intro n. induction n using lt_wf_ind. intro rank. induction rank using lt_wf_ind.
    intros c s z Rank Infinite Match Run End.
    inversion Infinite as [c0 child Des InfiniteChild]; subst.
    destruct (descends_simulation fs code c child C Des s Match) as [t [T [Mt Progress]]].
    destruct Progress as [Smaller | Positive].
    - destruct (steps_counted code s t T) as [k Prefix]. destruct k.
      + inversion Prefix; subst t.
        exact (H0 (configuration_rank child) ltac:(lia) child s z (Nat.le_refl _) InfiniteChild Mt Run End).
      + destruct (counted_prefix code (S k) s t Prefix n z Run End) as [left [Size Tail]].
        exact (H left ltac:(lia) (configuration_rank child) child t z (Nat.le_refl _) InfiniteChild Mt Tail End).
    - destruct Positive as [u [First Rest]].
      destruct (steps_counted code u t Rest) as [k RestCount].
      assert (Prefix : counted code (S k) s t) by (eapply counted_step; eauto).
      destruct (counted_prefix code (S k) s t Prefix n z Run End) as [left [Size Tail]].
      exact (H left ltac:(lia) (configuration_rank child) child t z (Nat.le_refl _) InfiniteChild Mt Tail End).
  }
  intros c s Infinite Match z Run. destruct (steps_counted code s z Run) as [n Count].
  destruct (mode z) eqn:Mode; auto; exfalso;
    eapply (NoTerminal n (configuration_rank c) c s z); eauto; congruence.
Qed.
CoInductive infinite_steps code : state -> Prop :=
| infinite_next s t : transition code s t -> infinite_steps code t -> infinite_steps code s.
Lemma running_forever code s :
  (forall z, steps code s z -> mode z = Running) -> infinite_steps code s.
Proof.
  revert s. cofix Forever. intros s Infinite.
  assert (M : mode s = Running) by (apply Infinite; constructor).
  destruct (running_progress code s M) as [t T]. eapply infinite_next; [exact T |].
  apply Forever. intros z Z. apply Infinite. eapply steps_cons; eauto.
Qed.
Corollary compiler_infinite_execution fs code c s : compilation_check fs code = true ->
  source_diverges (source_lookup fs) c -> matches_configuration fs code c s -> infinite_steps code s.
Proof. intros C Infinite Match. apply running_forever. eapply compiler_divergence_correct; eauto. Qed.
Lemma compiler_body_match fs code main : compilation_check fs code = true -> nth_error fs 0 = Some main ->
  exists s, steps code initial s /\
    matches_configuration fs code (Statement 0 (fun _ => 0%N) main (fun _ => 0%N) 0) s.
Proof.
  intros C Main. pose proof (compilation_verified fs code C) as V.
  destruct (checked_function fs code 0 main C Main) as [Valid [Layout Address]].
  cbn [Nat.eqb] in Layout, Address. rewrite Address in Layout.
  apply layout_append in Layout. destruct Layout as [Header BodyLayout].
  rewrite prologue_size in BodyLayout. cbn [prologue_width] in BodyLayout.
  cbn [prologue expression_layout] in Header. destruct Header as [EntryDecode _].
  pose proof (execution_one code initial Entry eq_refl EntryDecode) as T01.
  set (s := execute code initial Entry).
  assert (I0 : machine_valid code initial).
  { split; [apply initial_well_formed |]. split; [apply initial_canonical | now apply accepted_initial]. }
  exists s. split; auto. exists true. split.
  - unfold ready. split; [exact (machine_valid_steps code initial s V I0 T01) |].
    split; [reflexivity |]. split; [reflexivity |]. split.
    + intros n N. reflexivity.
    + split; reflexivity.
  - split; auto.
Qed.
Theorem compiled_program_faults fs code main f m h :
  compilation_check fs code = true -> nth_error fs 0 = Some main ->
  raises (source_lookup fs) (Statement 0 (fun _ => 0%N) main (fun _ => 0%N) 0) f m h ->
  fault_run code initial f m h.
Proof.
  intros C Main E. destruct (compiler_body_match fs code main C Main) as [s [T Match]].
  eapply fault_prefix; [exact T |]. eapply compiler_fault_correct; eauto.
Qed.
Theorem compiled_program_diverges fs code main :
  compilation_check fs code = true -> nth_error fs 0 = Some main ->
  source_diverges (source_lookup fs) (Statement 0 (fun _ => 0%N) main (fun _ => 0%N) 0) -> diverges code.
Proof.
  intros C Main Infinite. destruct (compiler_body_match fs code main C Main) as [s [T Match]].
  destruct (steps_counted code initial s T) as [k Prefix].
  intros z Run. destruct (mode z) eqn:Mode; auto; exfalso;
    destruct (steps_counted code initial z Run) as [n Count];
    destruct (counted_prefix code k initial s Prefix n z Count ltac:(congruence)) as [left [_ Tail]];
    pose proof (compiler_divergence_correct fs code C _ _ Infinite Match z (counted_steps code left s z Tail));
    congruence.
Qed.
Theorem optimised_program_terminates fs code optimised main value env m h :
  compilation_check fs code = true -> optimisation_pipeline code optimised -> nth_error fs 0 = Some main ->
  evaluates_statement (source_lookup fs) 0 (fun _ => 0%N) main (fun _ => 0%N) 0 (Some value) env m h ->
  exists t, steps optimised initial t /\ mode t = Stopped /\ regs t 0 = value /\ mem t = m /\ frontier t = h.
Proof.
  intros C Pipeline Main E.
  destruct (compiled_program_terminates fs code main value env m h C Main E) as [s [T [M [R [Mem F]]]]].
  destruct (optimisation_pipeline_correct code optimised Pipeline s T ltac:(congruence)) as [t [U [_ [Mt [Memt [Ft [Rt _]]]]]]].
  exists t. split; auto. rewrite <- Mt, <- (Rt 0), <- Memt, <- Ft. auto.
Qed.
Theorem optimised_program_faults fs code optimised main f m h :
  compilation_check fs code = true -> optimisation_pipeline code optimised -> nth_error fs 0 = Some main ->
  raises (source_lookup fs) (Statement 0 (fun _ => 0%N) main (fun _ => 0%N) 0) f m h ->
  fault_run optimised initial f m h.
Proof.
  intros C Pipeline Main E.
  destruct (compiled_program_faults fs code main f m h C Main E) as [s [T [M [Mem F]]]].
  destruct (optimisation_pipeline_correct code optimised Pipeline s T ltac:(congruence)) as [t [U [_ [Mt [Memt [Ft _]]]]]].
  exists t. split; auto. rewrite <- Mt, <- Memt, <- Ft. auto.
Qed.
Theorem optimised_program_diverges fs code optimised main :
  compilation_check fs code = true -> optimisation_pipeline code optimised -> nth_error fs 0 = Some main ->
  source_diverges (source_lookup fs) (Statement 0 (fun _ => 0%N) main (fun _ => 0%N) 0) -> diverges optimised.
Proof.
  intros C Pipeline Main Infinite. apply (proj1 (optimisation_pipeline_divergence code optimised Pipeline)).
  eapply compiled_program_diverges; eauto.
Qed.
Lemma source_infinite_loop program depth env m h :
  source_diverges program (Statement depth env (While (Literal 1%N) Skip) m h).
Proof.
  cofix Loop. eapply diverges_below; [|exact Loop].
  eapply descend_while_next with (x := word 1%N); try constructor. discriminate.
Qed.
Lemma source_steps_trans program s t u : source_steps program s t -> source_steps program t u -> source_steps program s u.
Proof. intro T. induction T; eauto using source_steps. Qed.
Definition source_configuration c k :=
  match c with
  | Expression depth env e m h => SourceState (Evaluate e) env m h depth k Running
  | Statement depth env body m h => SourceState (Execute body) env m h depth k Running end.
Definition statement_result_control result := match result with None => Execute Skip | Some v => Returning v end.
Local Ltac source_tick :=
  eapply source_cons;
  [constructor; cbn [source_step source_next source_control locals source_memory source_frontier source_depth continuations source_mode]; reflexivity |].
Lemma compare_word op x y : word (compare_values op x y) = compare_values op x y.
Proof.
  destruct op; cbn [compare_values];
  repeat match goal with |- context [if ?b then _ else _] => destruct b end; reflexivity.
Qed.
Theorem source_normal_execution program :
  (forall depth env e m h x m1 h1, evaluates_expression program depth env e m h x m1 h1 ->
    forall k, source_steps program (SourceState (Evaluate e) env m h depth k Running)
      (SourceState (Value x) env m1 h1 depth k Running)) /\
  (forall depth env body m h result env1 m1 h1, evaluates_statement program depth env body m h result env1 m1 h1 ->
    forall k, source_steps program (SourceState (Execute body) env m h depth k Running)
      (SourceState (statement_result_control result) env1 m1 h1 depth k Running)).
Proof.
  apply evaluation_ind; intros depth env.
  - intros n m h k. source_tick. constructor.
  - intros n m h k. source_tick. constructor.
  - intros op a b m h x m1 h1 y m2 h2 z E1 IH1 E2 IH2 Op k.
    source_tick. eapply source_steps_trans; [apply IH1 |]. source_tick.
    eapply source_steps_trans; [apply IH2 |].
    eapply source_cons; [constructor; cbn [source_step source_next source_control locals source_memory source_frontier source_depth continuations source_mode]; rewrite Op; reflexivity | constructor].
  - intros op a b m h x m1 h1 y m2 h2 E1 IH1 E2 IH2 k.
    source_tick. eapply source_steps_trans; [apply IH1 |]. source_tick.
    eapply source_steps_trans; [apply IH2 |]. rewrite compare_word. source_tick. constructor.
  - intros a m h x m1 h1 E IH Bound k.
    source_tick. eapply source_steps_trans; [apply IH |].
    assert (B : (N.to_nat x + 8 <=? h1) = true) by now apply Nat.leb_le.
    eapply source_cons; [constructor; cbn [source_step source_next source_control locals source_memory source_frontier source_depth continuations source_mode]; rewrite B; reflexivity | constructor].
  - intros a m h x m1 h1 E IH Bound k.
    source_tick. eapply source_steps_trans; [apply IH |].
    assert (B : (h1 + N.to_nat x <=? memory_size) = true) by now apply Nat.leb_le.
    eapply source_cons; [constructor; cbn [source_step source_next source_control locals source_memory source_frontier source_depth continuations source_mode]; rewrite B; reflexivity | constructor].
  - intros m h k. source_tick. constructor.
  - intros f a body m h x m1 h1 result env2 m2 h2 E IH Lookup Nonroot Capacity Body IHBody k.
    source_tick. eapply source_steps_trans; [apply IH |].
    assert (Cap : (depth <? stack_size) = true) by now apply Nat.ltb_lt.
    eapply source_cons.
    + constructor. cbn [source_step source_next source_control locals source_memory source_frontier source_depth continuations source_mode]. rewrite Lookup, Cap. reflexivity.
    + eapply source_steps_trans; [apply IHBody |]. source_tick. constructor.
  - intros m h k. constructor.
  - intros n e m h x m1 h1 E IH k.
    source_tick. eapply source_steps_trans; [apply IH |]. source_tick. constructor.
  - intros e m h x m1 h1 E IH k.
    source_tick. eapply source_steps_trans; [apply IH |]. source_tick. constructor.
  - intros a b m h x m1 h1 y m2 h2 E1 IH1 E2 IH2 Bound k.
    source_tick. eapply source_steps_trans; [apply IH1 |]. source_tick.
    eapply source_steps_trans; [apply IH2 |].
    assert (B : (N.to_nat x + 8 <=? h2) = true) by now apply Nat.leb_le.
    eapply source_cons; [constructor; cbn [source_step source_next source_control locals source_memory source_frontier source_depth continuations source_mode]; rewrite B; reflexivity | constructor].
  - intros e m h x m1 h1 E IH Bound k.
    source_tick. eapply source_steps_trans; [apply IH |].
    assert (B : (N.to_nat x <=? h1) = true) by now apply Nat.leb_le.
    eapply source_cons; [constructor; cbn [source_step source_next source_control locals source_memory source_frontier source_depth continuations source_mode]; rewrite B; reflexivity | constructor].
  - intros a b m h env1 m1 h1 result env2 m2 h2 E1 IH1 E2 IH2 k.
    source_tick. eapply source_steps_trans; [apply IH1 |]. source_tick. apply IH2.
  - intros a b m h x env1 m1 h1 E IH k.
    source_tick. eapply source_steps_trans; [apply IH |]. source_tick. constructor.
  - intros e a b m h x m1 h1 result env2 m2 h2 E IH Nonzero Body IHBody k.
    source_tick. eapply source_steps_trans; [apply IH |].
    apply N.eqb_neq in Nonzero. eapply source_cons.
    + constructor. cbn [source_step source_next source_control locals source_memory source_frontier source_depth continuations source_mode]. rewrite Nonzero. reflexivity.
    + apply IHBody.
  - intros e a b m h m1 h1 result env2 m2 h2 E IH Body IHBody k.
    source_tick. eapply source_steps_trans; [apply IH |]. source_tick. apply IHBody.
  - intros e body m h m1 h1 E IH k.
    source_tick. eapply source_steps_trans; [apply IH |]. source_tick. constructor.
  - intros e body m h x m1 h1 env1 m2 h2 result env2 m3 h3 E IH Nonzero Body IHBody Loop IHLoop k.
    source_tick. eapply source_steps_trans; [apply IH |].
    apply N.eqb_neq in Nonzero. eapply source_cons.
    + constructor. cbn [source_step source_next source_control locals source_memory source_frontier source_depth continuations source_mode]. rewrite Nonzero. reflexivity.
    + source_tick. eapply source_steps_trans; [apply IHBody |]. source_tick. apply IHLoop.
  - intros e body m h x m1 h1 result env1 m2 h2 E IH Nonzero Body IHBody k.
    source_tick. eapply source_steps_trans; [apply IH |].
    apply N.eqb_neq in Nonzero. eapply source_cons.
    + constructor. cbn [source_step source_next source_control locals source_memory source_frontier source_depth continuations source_mode]. rewrite Nonzero. reflexivity.
    + source_tick. eapply source_steps_trans; [apply IHBody |]. source_tick. constructor.
  - intros e m h x m1 h1 E IH k.
    source_tick. eapply source_steps_trans; [apply IH |]. source_tick. constructor.
Qed.
Definition source_positive program s t := exists u, source_transition program s u /\ source_steps program u t.
Lemma source_positive_steps program s t : source_positive program s t -> source_steps program s t.
Proof. intros [u [U T]]. eapply source_cons; eauto. Qed.
Local Ltac source_start :=
  eexists; split;
  [constructor; cbn [source_step source_next source_control locals source_memory source_frontier source_depth continuations source_mode]; reflexivity |].
Theorem descends_source_execution program c child : descends program c child ->
  forall k, exists k', source_positive program (source_configuration c k) (source_configuration child k').
Proof.
  intro Des. destruct Des; intro k; unfold source_positive; cbn [source_configuration].
  - exists (LeftOperand op b :: k). source_start. constructor.
  - exists (RightOperand op x :: k). source_start.
    eapply source_steps_trans; [exact (proj1 (source_normal_execution program) _ _ _ _ _ _ _ _ H _) |]. source_tick. constructor.
  - exists (LeftComparison op b :: k). source_start. constructor.
  - exists (RightComparison op x :: k). source_start.
    eapply source_steps_trans; [exact (proj1 (source_normal_execution program) _ _ _ _ _ _ _ _ H _) |]. source_tick. constructor.
  - exists (ReadAddress :: k). source_start. constructor.
  - exists (NewSize :: k). source_start. constructor.
  - exists (InvokeArgument f :: k). source_start. constructor.
  - exists (Restore env :: k). source_start.
    eapply source_steps_trans; [exact (proj1 (source_normal_execution program) _ _ _ _ _ _ _ _ H _) |].
    assert (Cap : (d <? stack_size) = true) by now apply Nat.ltb_lt.
    eapply source_cons.
    + constructor. cbn [source_step source_next source_control locals source_memory source_frontier source_depth continuations source_mode]. rewrite H0, Cap. reflexivity.
    + constructor.
  - exists (SaveLocal n :: k). source_start. constructor.
  - exists (DiscardValue :: k). source_start. constructor.
  - exists (WriteAddress b :: k). source_start. constructor.
  - exists (WriteValue x :: k). source_start.
    eapply source_steps_trans; [exact (proj1 (source_normal_execution program) _ _ _ _ _ _ _ _ H _) |]. source_tick. constructor.
  - exists (ResetValue :: k). source_start. constructor.
  - exists (Then b :: k). source_start. constructor.
  - exists k. source_start.
    eapply source_steps_trans; [exact (proj2 (source_normal_execution program) _ _ _ _ _ _ _ _ _ H _) |]. source_tick. constructor.
  - exists (Choose a b :: k). source_start. constructor.
  - exists k. source_start.
    eapply source_steps_trans; [exact (proj1 (source_normal_execution program) _ _ _ _ _ _ _ _ H _) |]. source_tick. constructor.
  - exists (Choose (Sequence body (While e body)) Skip :: k). source_start. constructor.
  - exists (Then (While e body) :: k). source_start.
    eapply source_steps_trans; [exact (proj1 (source_normal_execution program) _ _ _ _ _ _ _ _ H _) |].
    apply N.eqb_neq in H0. eapply source_cons.
    + constructor. cbn [source_step source_next source_control locals source_memory source_frontier source_depth continuations source_mode]. rewrite H0. reflexivity.
    + source_tick. constructor.
  - exists k. source_start.
    eapply source_steps_trans; [exact (proj1 (source_normal_execution program) _ _ _ _ _ _ _ _ H _) |].
    apply N.eqb_neq in H0. eapply source_cons.
    + constructor. cbn [source_step source_next source_control locals source_memory source_frontier source_depth continuations source_mode]. rewrite H0. reflexivity.
    + source_tick.
      eapply source_steps_trans; [exact (proj2 (source_normal_execution program) _ _ _ _ _ _ _ _ _ H1 _) |]. source_tick. constructor.
  - exists (ReturnValue :: k). source_start. constructor.
Qed.
Theorem source_local_fault_execution program c f m h : local_fault program c f m h ->
  forall k, exists t, source_steps program (source_configuration c k) t /\
    source_mode t = Fault f /\ source_memory t = m /\ source_frontier t = h.
Proof.
  intro E. destruct E; intro k; cbn [source_configuration].
  - eexists. split.
    + source_tick. eapply source_steps_trans; [exact (proj1 (source_normal_execution program) _ _ _ _ _ _ _ _ H _) |]. source_tick.
      eapply source_steps_trans; [exact (proj1 (source_normal_execution program) _ _ _ _ _ _ _ _ H0 _) |].
      eapply source_cons.
      * constructor. cbn [source_step source_next source_control locals source_memory source_frontier source_depth continuations source_mode]. rewrite H1. reflexivity.
      * constructor.
    + repeat split; reflexivity.
  - eexists. split.
    + source_tick. eapply source_steps_trans; [exact (proj1 (source_normal_execution program) _ _ _ _ _ _ _ _ H _) |].
      assert (B : (N.to_nat x + 8 <=? h1) = false) by now apply Nat.leb_gt.
      eapply source_cons.
      * constructor. cbn [source_step source_next source_control locals source_memory source_frontier source_depth continuations source_mode]. rewrite B. reflexivity.
      * constructor.
    + repeat split; reflexivity.
  - eexists. split.
    + source_tick. eapply source_steps_trans; [exact (proj1 (source_normal_execution program) _ _ _ _ _ _ _ _ H _) |].
      assert (B : (h1 + N.to_nat x <=? memory_size) = false) by now apply Nat.leb_gt.
      eapply source_cons.
      * constructor. cbn [source_step source_next source_control locals source_memory source_frontier source_depth continuations source_mode]. rewrite B. reflexivity.
      * constructor.
    + repeat split; reflexivity.
  - eexists. split.
    + source_tick. eapply source_steps_trans; [exact (proj1 (source_normal_execution program) _ _ _ _ _ _ _ _ H _) |].
      assert (Cap : (d <? stack_size) = false) by now apply Nat.ltb_ge.
      eapply source_cons.
      * constructor. cbn [source_step source_next source_control locals source_memory source_frontier source_depth continuations source_mode]. rewrite H0, Cap. reflexivity.
      * constructor.
    + repeat split; reflexivity.
  - eexists. split.
    + source_tick. eapply source_steps_trans; [exact (proj1 (source_normal_execution program) _ _ _ _ _ _ _ _ H _) |]. source_tick.
      eapply source_steps_trans; [exact (proj1 (source_normal_execution program) _ _ _ _ _ _ _ _ H0 _) |].
      assert (B : (N.to_nat x + 8 <=? h2) = false) by now apply Nat.leb_gt.
      eapply source_cons.
      * constructor. cbn [source_step source_next source_control locals source_memory source_frontier source_depth continuations source_mode]. rewrite B. reflexivity.
      * constructor.
    + repeat split; reflexivity.
  - eexists. split.
    + source_tick. eapply source_steps_trans; [exact (proj1 (source_normal_execution program) _ _ _ _ _ _ _ _ H _) |].
      assert (B : (N.to_nat x <=? h1) = false) by now apply Nat.leb_gt.
      eapply source_cons.
      * constructor. cbn [source_step source_next source_control locals source_memory source_frontier source_depth continuations source_mode]. rewrite B. reflexivity.
      * constructor.
    + repeat split; reflexivity.
Qed.
Theorem source_fault_execution program c f m h : raises program c f m h ->
  forall k, exists t, source_steps program (source_configuration c k) t /\
    source_mode t = Fault f /\ source_memory t = m /\ source_frontier t = h.
Proof.
  intro E. induction E; intro k.
  - now apply source_local_fault_execution.
  - destruct (descends_source_execution program c child H k) as [k' Prefix].
    destruct (IHE k') as [t [T O]]. exists t. split; auto.
    exact (source_steps_trans program _ _ _ (source_positive_steps program _ _ Prefix) T).
Qed.
Inductive source_counted program : nat -> source_state -> source_state -> Prop :=
| source_counted_zero s : source_counted program 0 s s
| source_counted_step n s t u : source_transition program s t -> source_counted program n t u ->
    source_counted program (S n) s u.
Lemma source_steps_counted program s t : source_steps program s t -> exists n, source_counted program n s t.
Proof.
  intro T. induction T.
  - exists 0. constructor.
  - destruct IHT as [n C]. exists (S n). eauto using source_counted.
Qed.
Lemma source_transition_running program s t : source_transition program s t -> source_mode s = Running.
Proof.
  intros T. inversion T as [s' t' E]. unfold source_step in E.
  destruct (source_mode s); congruence.
Qed.
Lemma source_counted_prefix program k s a : source_counted program k s a ->
  forall n z, source_counted program n s z -> source_mode z <> Running ->
  exists m, n = k + m /\ source_counted program m a z.
Proof.
  intro H. induction H; intros n0 z E Z.
  - exists n0. auto.
  - inversion E as [|n' s' t' z' T' E']; subst.
    + exfalso. apply Z. eauto using source_transition_running.
    + assert (t = t') by (eapply source_deterministic; eauto). subst t'.
      destruct (IHsource_counted _ _ E' Z) as [m [L C]]. exists m. split; auto. lia.
Qed.
Theorem source_divergence_execution program c : source_diverges program c ->
  forall k z, source_steps program (source_configuration c k) z -> source_mode z = Running.
Proof.
  revert c.
  assert (NoTerminal : forall n c k z, source_diverges program c ->
    source_counted program n (source_configuration c k) z -> source_mode z <> Running -> False).
  {
    intro n. induction n using lt_wf_ind. intros c k z Infinite Run End.
    inversion Infinite as [c0 child Des InfiniteChild]; subst.
    destruct (descends_source_execution program c child Des k) as [k' [u [First Rest]]].
    destruct (source_steps_counted program u (source_configuration child k') Rest) as [a A].
    assert (Prefix : source_counted program (S a) (source_configuration c k) (source_configuration child k'))
      by (eapply source_counted_step; eauto).
    destruct (source_counted_prefix program (S a) (source_configuration c k)
      (source_configuration child k') Prefix n z Run End) as [left [Size Tail]].
    exact (H left ltac:(lia) child k' z InfiniteChild Tail End).
  }
  intros c Infinite k z Run. destruct (source_steps_counted program _ _ Run) as [n Count].
  destruct (source_mode z) eqn:Mode; auto; exfalso;
    exact (NoTerminal n c k z Infinite Count ltac:(congruence)).
Qed.
CoInductive source_infinite_steps program : source_state -> Prop :=
| source_infinite_next s t : source_transition program s t -> source_infinite_steps program t ->
    source_infinite_steps program s.
Lemma source_running_progress program s : source_mode s = Running -> exists t, source_transition program s t.
Proof.
  intro M. assert (E : exists t, source_step program s = Some t).
  { unfold source_step. rewrite M. eexists. reflexivity. }
  destruct E as [t T]. exists t. now constructor.
Qed.
Lemma source_running_forever program s :
  (forall z, source_steps program s z -> source_mode z = Running) -> source_infinite_steps program s.
Proof.
  revert s. cofix Forever. intros s Infinite.
  assert (M : source_mode s = Running) by (apply Infinite; constructor).
  destruct (source_running_progress program s M) as [t T]. eapply source_infinite_next; [exact T |].
  apply Forever. intros z Z. apply Infinite. eapply source_cons; eauto.
Qed.
Corollary source_divergence_infinite program c k : source_diverges program c ->
  source_infinite_steps program (source_configuration c k).
Proof. intro D. apply source_running_forever. intros z Z. eapply source_divergence_execution; eauto. Qed.
Theorem source_program_normal program main value env m h :
  evaluates_statement program 0 (fun _ => 0%N) main (fun _ => 0%N) 0 (Some value) env m h ->
  source_steps program (source_initial main) (SourceState (Value value) env m h 0 [] Stopped).
Proof.
  intro E. eapply source_steps_trans; [exact (proj2 (source_normal_execution program) _ _ _ _ _ _ _ _ _ E []) |].
  source_tick. constructor.
Qed.
Lemma source_terminal_unique program s a b : source_steps program s a -> source_steps program s b ->
  source_mode a <> Running -> source_mode b <> Running -> a = b.
Proof.
  intros A. revert b. induction A; intros b B EndA EndB.
  - inversion B; subst; auto. exfalso. apply EndA. eauto using source_transition_running.
  - inversion B; subst.
    + exfalso. apply EndB. eauto using source_transition_running.
    + assert (t = t0) by (eapply source_deterministic; eauto). subst t0. eauto.
Qed.
Theorem executable_source_normal_agrees program main value env m h :
  evaluates_statement program 0 (fun _ => 0%N) main (fun _ => 0%N) 0 (Some value) env m h ->
  forall t, source_steps program (source_initial main) t -> source_mode t <> Running ->
  source_mode t = Stopped /\ source_control t = Value value /\ source_memory t = m /\ source_frontier t = h.
Proof.
  intros E t T End.
  pose proof (source_program_normal program main value env m h E) as Run.
  assert (Eq : t = SourceState (Value value) env m h 0 [] Stopped)
    by (eapply source_terminal_unique; eauto; discriminate).
  subst t. repeat split; reflexivity.
Qed.
Theorem executable_source_fault_agrees program c f m h : raises program c f m h ->
  forall k t, source_steps program (source_configuration c k) t -> source_mode t <> Running ->
  source_mode t = Fault f /\ source_memory t = m /\ source_frontier t = h.
Proof.
  intros E k t T End. destruct (source_fault_execution program c f m h E k) as [u [U [M [Mem F]]]].
  assert (Eq : t = u) by (eapply source_terminal_unique; eauto; congruence).
  subst t. auto.
Qed.
Theorem compiled_program_normal fs code main result env m h :
  compilation_check fs code = true -> nth_error fs 0 = Some main ->
  evaluates_statement (source_lookup fs) 0 (fun _ => 0%N) main (fun _ => 0%N) 0 result env m h ->
  exists value t, result = Some value /\ steps code initial t /\ mode t = Stopped /\
    regs t 0 = value /\ mem t = m /\ frontier t = h.
Proof.
  intros C Main E.
  destruct (guaranteed_return_sound (source_lookup fs) main 0 (fun _ => 0%N)
    (fun _ => 0%N) 0 result env m h E (checked_return fs code 0 main C Main)) as [v R].
  subst result. destruct (compiled_program_terminates fs code main v env m h C Main E) as [t T].
  exists v, t. auto.
Qed.
Theorem encoded_program_normal fs code main result env m h :
  compile_bytes fs = Some code -> nth_error fs 0 = Some main ->
  evaluates_statement (source_lookup fs) 0 (fun _ => 0%N) main (fun _ => 0%N) 0 result env m h ->
  exists value t, result = Some value /\ steps code initial t /\ mode t = Stopped /\
    regs t 0 = value /\ mem t = m /\ frontier t = h.
Proof. intro C. apply compiled_program_normal. exact (proj1 (compile_bytes_checked fs code C)). Qed.
Theorem encoded_program_faults fs code main f m h :
  compile_bytes fs = Some code -> nth_error fs 0 = Some main ->
  raises (source_lookup fs) (Statement 0 (fun _ => 0%N) main (fun _ => 0%N) 0) f m h ->
  fault_run code initial f m h.
Proof. intro C. apply compiled_program_faults. exact (proj1 (compile_bytes_checked fs code C)). Qed.
Theorem encoded_program_diverges fs code main :
  compile_bytes fs = Some code -> nth_error fs 0 = Some main ->
  source_diverges (source_lookup fs) (Statement 0 (fun _ => 0%N) main (fun _ => 0%N) 0) -> diverges code.
Proof. intro C. apply compiled_program_diverges. exact (proj1 (compile_bytes_checked fs code C)). Qed.

Theorem text_compilation_correct chars certs code : compile_text chars certs = Some code ->
  exists fs, parses_program chars fs /\ compile_bytes fs = Some code /\
    (forall main result env m h, nth_error fs 0 = Some main ->
      evaluates_statement (source_lookup fs) 0 (fun _ => 0%N) main (fun _ => 0%N) 0 result env m h ->
      exists value t, result = Some value /\ steps code initial t /\ mode t = Stopped /\
        regs t 0 = value /\ mem t = m /\ frontier t = h) /\
    (forall main f m h, nth_error fs 0 = Some main ->
      raises (source_lookup fs) (Statement 0 (fun _ => 0%N) main (fun _ => 0%N) 0) f m h ->
      fault_run code initial f m h) /\
    (forall main, nth_error fs 0 = Some main ->
      source_diverges (source_lookup fs) (Statement 0 (fun _ => 0%N) main (fun _ => 0%N) 0) -> diverges code).
Proof.
  intro C. destruct (compile_text_sound _ _ _ C) as [fs [Parsed Compiled]].
  exists fs. split; [exact Parsed |]. split; [exact Compiled |]. split.
  - intros. eapply encoded_program_normal; eauto.
  - split; intros; [eapply encoded_program_faults | eapply encoded_program_diverges]; eauto.
Qed.
Theorem text_normal_execution_simulation chars certs code : compile_text chars certs = Some code ->
  exists fs, parses_program chars fs /\
    forward_simulation (normal_execution fs) code (compilation_matches fs).
Proof.
  intro C. destruct (compile_text_sound _ _ _ C) as [fs [Parsed Compiled]].
  exists fs. split; [exact Parsed |]. apply compiled_normal_execution_simulation.
  exact (proj1 (compile_bytes_checked _ _ Compiled)).
Qed.
