From Stdlib Require Import List NArith Arith Bool Lia.
From Loosevm Require Import Syntax State Semantics Interpreter Verifier Source Compiler Encoding Frontend Simulation TotalSimulation.
Import ListNotations.
Local Opaque memory_size stack_size.

Inductive jump_path (code : list nat) : nat -> nat -> Prop :=
| jump_here p : jump_path code p p
| jump_next p q r : decode code p = Some (Jump q) -> jump_path code q r -> jump_path code p r.
Inductive exit_flow (code : list nat) : option nat -> option nat -> Prop :=
| exit_none out : exit_flow code None out
| exit_some p q : jump_path code p q -> exit_flow code (Some p) (Some q).

Section ControlFlow.
Variable code : list nat.
Variable address : nat -> nat.
Variable root : bool.
Inductive statement_code : statement -> nat -> option nat -> Prop :=
| statement_location body p entry actual out :
    jump_path code p entry -> command_code body entry actual -> exit_flow code actual out ->
    statement_code body p out
with command_code : statement -> nat -> option nat -> Prop :=
| command_skip p : command_code Skip p (Some p)
| command_assign n e p :
    expression_layout code p (emit_expression address e 9) ->
    decode code (p + expression_width e) = Some (Move (S n) 9) ->
    command_code (Assign n e) p (Some (p + expression_width e + 3))
| command_discard e p :
    expression_layout code p (emit_expression address e 9) ->
    command_code (Discard e) p (Some (p + expression_width e))
| command_write a b p :
    expression_layout code p (emit_expression address a 9) ->
    expression_layout code (p + expression_width a) (emit_expression address b 10) ->
    decode code (p + expression_width a + expression_width b) = Some (Store 9 10) ->
    command_code (Write a b) p (Some (p + expression_width a + expression_width b + 3))
| command_rewind e p :
    expression_layout code p (emit_expression address e 9) ->
    decode code (p + expression_width e) = Some (Reset 9) ->
    command_code (Rewind e) p (Some (p + expression_width e + 2))
| command_sequence a b p middle out :
    statement_code a p (Some middle) -> statement_code b middle out ->
    command_code (Sequence a b) p out
| command_sequence_return a b p : statement_code a p None -> command_code (Sequence a b) p None
| command_conditional e yes no p yes_pc out :
    expression_layout code p (emit_expression address e 9) ->
    decode code (p + expression_width e) = Some (Branch 9 yes_pc) ->
    statement_code yes yes_pc out -> statement_code no (p + expression_width e + 10) out ->
    command_code (Conditional e yes no) p out
| command_while e body p body_pc back_pc end_pc :
    expression_layout code p (emit_expression address e 9) ->
    decode code (p + expression_width e) = Some (Branch 9 body_pc) ->
    decode code (p + expression_width e + 10) = Some (Jump end_pc) ->
    statement_code body body_pc (Some back_pc) -> decode code back_pc = Some (Jump p) ->
    command_code (While e body) p (Some end_pc)
| command_return e p :
    expression_layout code p (emit_expression address e 9) ->
    decode code (p + expression_width e) = Some (Move 0 9) ->
    decode code (p + expression_width e + 3) = Some (exit_instruction root) ->
    command_code (Return e) p None.
End ControlFlow.

Lemma jump_path_trans code p q r : jump_path code p q -> jump_path code q r -> jump_path code p r.
Proof. intros A B. induction A; eauto using jump_path. Qed.
Lemma exit_flow_refl code out : exit_flow code out out.
Proof. destruct out; constructor. constructor. Qed.
Lemma exit_flow_trans code a b c : exit_flow code a b -> exit_flow code b c -> exit_flow code a c.
Proof.
  intros A B. inversion A; subst; [constructor |]. inversion B; subst.
  constructor. eauto using jump_path_trans.
Qed.
Lemma statement_code_before code address root body p q out :
  jump_path code p q -> statement_code code address root body q out -> statement_code code address root body p out.
Proof.
  intros Path Code. inversion Code as [body0 q0 entry actual out0 Next Command Flow]; subst.
  eapply statement_location with (entry := entry) (actual := actual).
  - eapply jump_path_trans; eassumption.
  - exact Command.
  - exact Flow.
Qed.
Lemma statement_code_after code address root body p a b :
  statement_code code address root body p a -> exit_flow code a b -> statement_code code address root body p b.
Proof.
  intros Code Flow. inversion Code as [body0 p0 entry actual out0 Path Command Before]; subst.
  eapply statement_location with (entry := entry) (actual := actual); [exact Path | exact Command |].
  eapply exit_flow_trans; eassumption.
Qed.
Fixpoint expression_cost e :=
  match e with
  | Literal _ | Local _ | Watermark => 1
  | Operation _ a b | Compare _ a b => expression_cost a + expression_cost b + 3
  | Read a | New a | Invoke _ a => expression_cost a + 2 end.
Fixpoint statement_cost body :=
  match body with
  | Skip => 0
  | Assign _ e | Discard e | Rewind e | Return e => expression_cost e + 2
  | Write a b => expression_cost a + expression_cost b + 3
  | Sequence a b => statement_cost a + statement_cost b + 2
  | Conditional e _ _ | While e _ => expression_cost e + 2 end.
Definition continuation_cost k :=
  match k with
  | LeftOperand _ b | LeftComparison _ b | WriteAddress b => expression_cost b + 2
  | Then next => statement_cost next + 1
  | Repeat e body => statement_cost (While e body) + 1
  | _ => 1 end.
Definition source_rank s :=
  (match source_control s with
  | Evaluate e => expression_cost e | Execute body => statement_cost body
  | _ => 0 end) + fold_right (fun k n => continuation_cost k + n) 0 (continuations s).

Definition restore_frame k := match k with Restore _ => true | _ => false end.
Section Continuations.
Variable fs : list statement.
Variable code : list nat.
Inductive expression_continuation : bool -> nat -> nat -> list continuation -> registers -> list frame -> Prop :=
| continuation_left root op b d p k r stack :
    valid_expression (length fs) b (S d) = true ->
    expression_layout code p (emit_expression (address_of fs) b (S d)) ->
    decode code (p + expression_width b) = Some (Binary op d d (S d)) ->
    expression_continuation root d (p + expression_width b + 4) k r stack ->
    expression_continuation root d p (LeftOperand op b :: k) r stack
| continuation_right root op x d p k r stack :
    9 <= d -> r d = x -> decode code p = Some (Binary op d d (S d)) ->
    expression_continuation root d (p + 4) k r stack ->
    expression_continuation root (S d) p (RightOperand op x :: k) r stack
| continuation_compare_left root op b d p k r stack :
    valid_expression (length fs) b (S d) = true ->
    expression_layout code p (emit_expression (address_of fs) b (S d)) ->
    expression_layout code (p + expression_width b) (comparison_code op d) ->
    expression_continuation root d (p + expression_width b + code_size (comparison_code op d)) k r stack ->
    expression_continuation root d p (LeftComparison op b :: k) r stack
| continuation_compare_right root op x d p k r stack :
    9 <= d -> r d = x -> expression_layout code p (comparison_code op d) ->
    expression_continuation root d (p + code_size (comparison_code op d)) k r stack ->
    expression_continuation root (S d) p (RightComparison op x :: k) r stack
| continuation_read root d p k r stack :
    decode code p = Some (Load d d) -> expression_continuation root d (p + 3) k r stack ->
    expression_continuation root d p (ReadAddress :: k) r stack
| continuation_new root d p k r stack :
    decode code p = Some (Alloc d d) -> expression_continuation root d (p + 3) k r stack ->
    expression_continuation root d p (NewSize :: k) r stack
| continuation_argument root f d p k r stack :
    0 < f < length fs -> decode code p = Some (Move 15 d) ->
    decode code (p + 3) = Some (Call (address_of fs f)) -> decode code (p + 12) = Some (Move d 0) ->
    expression_continuation root d (p + 15) k r stack ->
    expression_continuation root d p (InvokeArgument f :: k) r stack
| continuation_save root n p k r stack :
    n < 8 -> decode code p = Some (Move (S n) 9) ->
    statement_continuation root (Some (p + 3)) k stack ->
    expression_continuation root 9 p (SaveLocal n :: k) r stack
| continuation_write_address root e p k r stack :
    valid_expression (length fs) e 10 = true ->
    expression_layout code p (emit_expression (address_of fs) e 10) ->
    decode code (p + expression_width e) = Some (Store 9 10) ->
    statement_continuation root (Some (p + expression_width e + 3)) k stack ->
    expression_continuation root 9 p (WriteAddress e :: k) r stack
| continuation_write_value root a p k r stack :
    r 9 = a -> decode code p = Some (Store 9 10) ->
    statement_continuation root (Some (p + 3)) k stack ->
    expression_continuation root 10 p (WriteValue a :: k) r stack
| continuation_discard root p k r stack :
    statement_continuation root (Some p) k stack ->
    expression_continuation root 9 p (DiscardValue :: k) r stack
| continuation_reset root p k r stack :
    decode code p = Some (Reset 9) -> statement_continuation root (Some (p + 2)) k stack ->
    expression_continuation root 9 p (ResetValue :: k) r stack
| continuation_choose root yes no p yes_pc out k r stack :
    decode code p = Some (Branch 9 yes_pc) ->
    valid_statement (length fs) yes = true -> valid_statement (length fs) no = true ->
    statement_code code (address_of fs) root yes yes_pc out ->
    statement_code code (address_of fs) root no (p + 10) out ->
    statement_continuation root out k stack ->
    expression_continuation root 9 p (Choose yes no :: k) r stack
| continuation_return root p k r stack :
    decode code p = Some (Move 0 9) -> decode code (p + 3) = Some (exit_instruction root) ->
    returning_continuation root k stack ->
    expression_continuation root 9 p (ReturnValue :: k) r stack
with statement_continuation : bool -> option nat -> list continuation -> list frame -> Prop :=
| continuation_none root k stack :
    returning_continuation root k stack -> statement_continuation root None k stack
| continuation_then root next p out k stack :
    valid_statement (length fs) next = true -> statement_code code (address_of fs) root next p out ->
    statement_continuation root out k stack ->
    statement_continuation root (Some p) (Then next :: k) stack
| continuation_bridge root p q k stack :
    jump_path code p q -> statement_continuation root (Some q) k stack ->
    statement_continuation root (Some p) k stack
with returning_continuation : bool -> list continuation -> list frame -> Prop :=
| continuation_main : returning_continuation true [] []
| continuation_restore caller_root d p caller k saved stack :
    9 <= d < 15 -> boundary code p = true -> decode code p = Some (Move d 0) ->
    locals_match caller saved -> expression_continuation caller_root d (p + 3) k saved stack ->
    returning_continuation false (Restore caller :: k) (Frame p saved :: stack)
| continuation_unwind root item k stack :
    restore_frame item = false -> returning_continuation root k stack ->
    returning_continuation root (item :: k) stack.
End Continuations.

Section States.
Variable fs : list statement.
Variable code : list nat.
Inductive core_match : source_state -> state -> Prop :=
| core_expression depth env e m h k t root d :
    ready code depth env m h t -> 9 <= d -> valid_expression (length fs) e d = true ->
    expression_layout code (pc t) (emit_expression (address_of fs) e d) ->
    expression_continuation fs code root d (pc t + expression_width e) k (regs t) (frames t) ->
    core_match (SourceState (Evaluate e) env m h depth k Running) t
| core_value depth env v m h k t root d :
    ready code depth env m h t -> 9 <= d < 15 -> regs t d = v ->
    expression_continuation fs code root d (pc t) k (regs t) (frames t) ->
    core_match (SourceState (Value v) env m h depth k Running) t
| core_statement depth env body m h k t root out :
    ready code depth env m h t -> valid_statement (length fs) body = true ->
    statement_code code (address_of fs) root body (pc t) out ->
    statement_continuation fs code root out k (frames t) ->
    core_match (SourceState (Execute body) env m h depth k Running) t
| core_returning depth env v m h k t root :
    ready code depth env m h t -> regs t 0 = v -> decode code (pc t) = Some (exit_instruction root) ->
    returning_continuation fs code root k (frames t) ->
    core_match (SourceState (Returning v) env m h depth k Running) t.
Inductive cek_matches : source_state -> state -> Prop :=
| cek_running s t entry : steps code t entry -> core_match s entry -> cek_matches s t
| cek_stopped s t value : source_mode s = Stopped -> source_control s = Value value ->
    mode t = Stopped -> regs t 0 = value -> mem t = source_memory s -> frontier t = source_frontier s ->
    cek_matches s t
| cek_fault s t f : source_mode s = Fault f -> mode t = Fault f ->
    mem t = source_memory s -> frontier t = source_frontier s -> cek_matches s t.
End States.

Lemma core_running fs code s t : core_match fs code s t -> source_mode s = Running /\ mode t = Running.
Proof. intro M. inversion M; subst; unfold ready in *; cbn; tauto. Qed.
Lemma cek_result fs code s t : cek_matches fs code s t -> source_mode s = Stopped ->
  exists v, source_control s = Value v /\ mode t = Stopped /\ regs t 0 = v.
Proof.
  intros M StoppedMode. inversion M; subst.
  - destruct (core_running _ _ _ _ H0) as [SourceMode TargetMode]. congruence.
  - eexists. repeat split; eauto.
  - congruence.
Qed.
Lemma cek_fault_result fs code s t f : cek_matches fs code s t -> source_mode s = Fault f ->
  mode t = Fault f /\ mem t = source_memory s /\ frontier t = source_frontier s.
Proof.
  intros M FaultMode. inversion M; subst.
  - destruct (core_running _ _ _ _ H0) as [SourceMode TargetMode]. congruence.
  - congruence.
  - repeat split; congruence.
Qed.
Definition agrees_below d (before after : registers) := forall n, 0 < n < d -> after n = before n.
Lemma locals_agree_below env before after d : 9 <= d -> locals_match env before ->
  agrees_below d before after -> locals_match env after.
Proof. intros Bound Locals Agree n Local. rewrite Agree by lia. now apply Locals. Qed.
Lemma continuation_stable fs code root d p k before stack :
  expression_continuation fs code root d p k before stack ->
  forall after, agrees_below d before after -> expression_continuation fs code root d p k after stack.
Proof.
  intro K. induction K; intros after Agree; econstructor; eauto.
  all: try solve [unfold agrees_below in *; rewrite Agree by lia; assumption].
  all: match goal with IH : forall after, agrees_below _ _ after -> _ |- _ =>
    apply IH; unfold agrees_below in *; intros n Bound; apply Agree; lia end.
Qed.

Lemma statement_of_command code address root body p out : command_code code address root body p out ->
  statement_code code address root body p out.
Proof.
  intro C. eapply statement_location with (entry := p) (actual := out);
    [constructor | exact C | apply exit_flow_refl].
Qed.
Lemma skip_exit code address root p out : statement_code code address root Skip p out ->
  exists q, out = Some q /\ jump_path code p q.
Proof.
  intro C. inversion C as [body0 p0 entry actual out0 Path Command Flow]; subst.
  inversion Command; subst. inversion Flow; subst.
  eexists. split; [reflexivity |]. eapply jump_path_trans; eassumption.
Qed.
Lemma statement_continuation_return fs code root out k stack :
  statement_continuation fs code root out k stack -> returning_continuation fs code root k stack.
Proof.
  intro K. induction K; [assumption | | assumption].
  apply continuation_unwind; [reflexivity | assumption].
Qed.
Lemma statement_continuation_flow fs code root a b k stack :
  exit_flow code a b -> statement_continuation fs code root b k stack ->
  statement_continuation fs code root a k stack.
Proof.
  intros Flow K. inversion Flow; subst.
  - apply continuation_none. now apply statement_continuation_return in K.
  - eapply continuation_bridge; eassumption.
Qed.
Lemma statement_continuation_resume fs code root p k stack :
  statement_continuation fs code root (Some p) k stack ->
  exists next tail entry out, k = Then next :: tail /\ jump_path code p entry /\
    valid_statement (length fs) next = true /\ statement_code code (address_of fs) root next entry out /\
    statement_continuation fs code root out tail stack.
Proof.
  intro K. remember (Some p) as endpoint eqn:E. revert p E.
  induction K; intros point E; [discriminate | |].
  - inversion E; subst. do 4 eexists. repeat split; eauto using jump_here.
  - inversion E; subst. destruct (IHK q eq_refl) as [next [tail [entry [out [Next [Path Rest]]]]]].
    exists next, tail, entry, out. split; [exact Next |]. split; [|exact Rest].
    eapply jump_path_trans; eassumption.
Qed.
Lemma at_pc_self s : mode s = Running -> at_pc s (pc s) = s.
Proof. destruct s as [p r m h stack status]; cbn; intro M; subst status; reflexivity. Qed.
Lemma jump_path_execution code p q : verify code = true -> jump_path code p q ->
  forall s, machine_valid code s -> mode s = Running -> pc s = p -> steps code s (at_pc s q).
Proof.
  intros Verified Path. induction Path; intros s Valid Mode Position.
  - rewrite <- Position, at_pc_self by assumption. constructor.
  - assert (Decoded : decode code (pc s) = Some (Jump q)) by congruence.
    destruct Valid as [Well [Canonical Structural]].
    pose proof (checked_boundary code (pc s) Verified (proj1 Structural)) as Guard.
    unfold check_at in Guard. rewrite Decoded in Guard.
    assert (Take : steps code s (at_pc s q)).
    { pose proof (execution_one code s (Jump q) Mode Decoded) as Take.
      change (steps code s (if local_target code (pc s) q then at_pc s q else finish s (Fault Target))) in Take.
      now rewrite Guard in Take. }
    eapply steps_trans; [exact Take |].
    change (steps code (at_pc s q) (at_pc (at_pc s q) r)).
    apply IHPath; [eapply machine_valid_steps; eauto; unfold machine_valid; tauto | reflexivity | reflexivity].
Qed.
Lemma exit_instruction_width root : width (exit_instruction root) = 1.
Proof. now destruct root. Qed.

Definition administrative_source s :=
  match source_control s with
  | Evaluate (Operation _ _ _) | Evaluate (Compare _ _ _)
  | Evaluate (Read _) | Evaluate (New _) | Evaluate (Invoke _ _) => true
  | Execute Skip => match continuations s with Then _ :: _ | Repeat _ _ :: _ => true | _ => false end
  | Execute _ => true
  | Value _ => match continuations s with
      | LeftOperand _ _ :: _ | LeftComparison _ _ :: _ | WriteAddress _ :: _ | DiscardValue :: _ => true
      | _ => false end
  | Returning _ => match continuations s with [] | Restore _ :: _ => false | _ => true end
  | _ => false end.
Lemma administrative_rank program s t : source_step program s = Some t -> administrative_source s = true ->
  source_rank t < source_rank s.
Proof.
  intros Step Administrative.
  destruct s as [c env m h depth k status]. destruct status;
    cbn [source_step source_mode source_control continuations] in Step; try discriminate.
  destruct c as [e | v | body | v].
  - destruct e; cbn [administrative_source] in Administrative; try discriminate;
      inversion Step; subst; cbv [source_rank source_next source_control continuations]; cbn [fold_right expression_cost statement_cost continuation_cost]; lia.
  - destruct k as [|item k]; [discriminate Administrative |].
    destruct item; cbn [administrative_source] in Administrative; try discriminate;
      inversion Step; subst; cbv [source_rank source_next source_control continuations]; cbn [fold_right expression_cost statement_cost continuation_cost]; lia.
  - destruct body; cbn [administrative_source] in Administrative;
      try (inversion Step; subst; cbv [source_rank source_next source_control continuations]; cbn [fold_right expression_cost statement_cost continuation_cost]; lia).
    destruct k as [|item k]; [discriminate Administrative |].
    destruct item; cbn [administrative_source] in Administrative; try discriminate;
      inversion Step; subst; cbv [source_rank source_next source_control continuations]; cbn [fold_right expression_cost statement_cost continuation_cost]; lia.
  - destruct k as [|item k]; [discriminate Administrative |].
    destruct item; cbn [administrative_source] in Administrative; try discriminate;
      inversion Step; subst; cbv [source_rank source_next source_control continuations]; cbn [fold_right expression_cost statement_cost continuation_cost]; lia.
Qed.

Lemma layout_statement_code code address root body : forall p,
  expression_layout code p (emit_statement address root body p) ->
  statement_code code address root body p (Some (p + statement_width body)).
Proof.
  induction body as [|name e|e|a b|e|a IHa b IHb|e yes IHy no IHn|e body IHbody|e];
    intros p Layout; cbn [emit_statement] in Layout.
  - cbn [statement_width]. rewrite Nat.add_0_r. apply statement_of_command. constructor.
  - apply layout_append in Layout. destruct Layout as [Expression Tail].
    rewrite expression_size in Tail. cbn [expression_layout] in Tail. destruct Tail as [Move _].
    cbn [statement_width]. replace (p + (expression_width e + 3)) with (p + expression_width e + 3) by lia.
    apply statement_of_command. now apply command_assign.
  - apply statement_of_command. now apply command_discard.
  - apply layout_append in Layout. destruct Layout as [Left Tail]. rewrite expression_size in Tail.
    apply layout_append in Tail. destruct Tail as [Right Tail]. rewrite expression_size in Tail.
    cbn [expression_layout] in Tail. destruct Tail as [Store _].
    cbn [statement_width]. replace (p + (expression_width a + expression_width b + 3))
      with (p + expression_width a + expression_width b + 3) by lia.
    apply statement_of_command. now apply command_write.
  - apply layout_append in Layout. destruct Layout as [Expression Tail]. rewrite expression_size in Tail.
    cbn [expression_layout] in Tail. destruct Tail as [Reset _].
    cbn [statement_width]. replace (p + (expression_width e + 2)) with (p + expression_width e + 2) by lia.
    apply statement_of_command. now apply command_rewind.
  - apply layout_append in Layout. destruct Layout as [Left Right]. rewrite statement_size in Right.
    cbn [statement_width]. replace (p + (statement_width a + statement_width b))
      with (p + statement_width a + statement_width b) by lia.
    apply statement_of_command. eapply command_sequence; [apply IHa | apply IHb]; assumption.
  - apply layout_append in Layout. destruct Layout as [Test Tail]. rewrite expression_size in Tail.
    apply layout_append in Tail. destruct Tail as [Branch Tail].
    cbn [expression_layout] in Branch. destruct Branch as [Branch _].
    cbn [code_size width] in Tail.
    apply layout_append in Tail. destruct Tail as [No Tail]. rewrite statement_size in Tail.
    apply layout_append in Tail. destruct Tail as [Jump Yes].
    cbn [expression_layout] in Jump. destruct Jump as [Jump _]. cbn [code_size width] in Yes.
    pose proof (IHn _ No) as NoCode. pose proof (IHy _ Yes) as YesCode.
    apply statement_of_command. eapply command_conditional; [exact Test | exact Branch | |].
    + replace (p + statement_width (Conditional e yes no)) with
        (p + expression_width e + 10 + statement_width no + 9 + statement_width yes) by (cbn [statement_width]; lia).
      exact YesCode.
    + eapply statement_code_after; [exact NoCode |]. constructor.
      eapply jump_next; [exact Jump | constructor].
  - apply layout_append in Layout. destruct Layout as [Test Tail]. rewrite expression_size in Tail.
    apply layout_append in Tail. destruct Tail as [Guard Tail].
    cbn [expression_layout] in Guard. destruct Guard as [Branch [Exit _]]. cbn [code_size width] in Tail.
    apply layout_append in Tail. destruct Tail as [Body Back]. rewrite statement_size in Back.
    cbn [expression_layout] in Back. destruct Back as [Back _].
    apply statement_of_command. eapply command_while; [exact Test | exact Branch | exact Exit | | exact Back].
    apply IHbody. exact Body.
  - apply layout_append in Layout. destruct Layout as [Expression Tail]. rewrite expression_size in Tail.
    cbn [expression_layout] in Tail. destruct Tail as [Move [Exit _]].
    eapply statement_code_after with (a := None); [|constructor].
    apply statement_of_command. now apply command_return.
Qed.

Lemma statement_code_returns code address root body : guaranteed_return body = true ->
  forall p out, statement_code code address root body p out -> statement_code code address root body p None.
Proof.
  induction body as [|n e|e|a b|e|a IHa b IHb|e yes IHy no IHn|e body IHbody|e];
    cbn [guaranteed_return]; intros Returns p out Code; try discriminate.
  all: inversion Code as [body0 p0 entry actual out0 Path Command Flow]; subst.
  all: apply statement_code_before with (q := entry); [exact Path | apply statement_of_command].
  - apply orb_true_iff in Returns. inversion Command; subst.
    + destruct Returns as [Returns | Returns].
      * apply command_sequence_return. eapply IHa; eassumption.
      * eapply command_sequence; [eassumption |]. eapply IHb; eassumption.
    + apply command_sequence_return. assumption.
  - apply andb_true_iff in Returns. destruct Returns as [Yes No].
    inversion Command; subst. eapply command_conditional; [eassumption | eassumption | |].
    + eapply IHy; eassumption.
    + eapply IHn; eassumption.
  - inversion Command; subst. eapply command_return; eassumption.
Qed.
Lemma checked_function_returns fs code f body :
  compilation_check fs code = true -> nth_error fs f = Some body -> guaranteed_return body = true.
Proof.
  unfold compilation_check. rewrite !andb_true_iff. intros [[Nonempty Verified] Functions] Found.
  apply forallb_forall with (x := f) in Functions.
  - unfold function_check in Functions. rewrite Found, !andb_true_iff in Functions. tauto.
  - apply in_seq. split; [lia |]. apply nth_error_Some. rewrite Found. discriminate.
Qed.
Lemma checked_function_code fs code f body :
  compilation_check fs code = true -> nth_error fs f = Some body ->
  statement_code code (address_of fs) (Nat.eqb f 0) body
    (address_of fs f + prologue_width (Nat.eqb f 0)) None.
Proof.
  intros Checked Found. destruct (checked_function fs code f body Checked Found) as [Valid [Layout Target]].
  apply layout_append in Layout. destruct Layout as [Prologue Body]. rewrite prologue_size in Body.
  eapply statement_code_returns; [eapply checked_function_returns; eauto |].
  now apply layout_statement_code.
Qed.

Lemma expression_completion fs code depth env e m h k root d t v m1 h1 u :
  verify code = true -> ready code depth env m h t -> 9 <= d < 15 ->
  expression_run code t e d v m1 h1 u ->
  expression_continuation fs code root d (pc t + expression_width e) k (regs t) (frames t) ->
  core_match fs code (SourceState (Value (word v)) env m1 h1 depth k Running) u.
Proof.
  intros Verified Ready Bound Run K.
  pose proof (expression_ready code depth env e t d v m1 h1 u Verified
    (ready_self _ _ _ _ _ _ Ready) (proj1 Bound) Run) as Ready1.
  destruct Run as [Steps [Mode [Position [Value [Below [Memory [Frontier Stack]]]]]]].
  eapply core_value with (root := root) (d := d); eauto.
  rewrite Position, Stack. eapply continuation_stable; [exact K | exact Below].
Qed.

Lemma evaluate_simulation fs code depth env e m h k root d t :
  compilation_check fs code = true -> ready code depth env m h t -> 9 <= d ->
  valid_expression (length fs) e d = true ->
  expression_layout code (pc t) (emit_expression (address_of fs) e d) ->
  expression_continuation fs code root d (pc t + expression_width e) k (regs t) (frames t) ->
  exists u, steps code t u /\
    core_match fs code
      (match source_step (source_lookup fs) (SourceState (Evaluate e) env m h depth k Running) with
       | Some next => next | None => SourceState (Evaluate e) env m h depth k Running end) u /\
    (administrative_source (SourceState (Evaluate e) env m h depth k Running) = false -> positive_steps code t u).
Proof.
  intros Checked Ready Bound Valid Layout K.
  pose proof (compilation_verified fs code Checked) as Verified.
  pose proof (expression_head_valid _ _ _ Valid) as Upper.
  destruct e as [n|n|op a b|op a b|a|a|f a|]; cbn [source_step source_next source_mode source_control continuations locals
    source_memory source_frontier source_depth]; cbn [administrative_source source_control].
  - destruct (normal_expression fs code depth env (Literal n) m h (word n) m h t d Checked
      (eval_literal _ _ _ _ _ _) Ready Bound Valid Layout) as [u [Run Ready1]].
    exists u. split; [exact (proj1 Run) |]. split.
    + rewrite <- (word_idempotent n). eapply expression_completion with (t := t) (e := Literal n) (root := root); eauto; lia.
    + intros _. now apply expression_positive in Run.
  - destruct (normal_expression fs code depth env (Local n) m h (word (env n)) m h t d Checked
      (eval_local _ _ _ _ _ _) Ready Bound Valid Layout) as [u [Run Ready1]].
    exists u. split; [exact (proj1 Run) |]. split.
    + rewrite <- (word_idempotent (env n)). eapply expression_completion with (t := t) (e := Local n) (root := root); eauto; lia.
    + intros _. now apply expression_positive in Run.
  - cbn [valid_expression] in Valid. rewrite !andb_true_iff in Valid. destruct Valid as [_ [Va Vb]].
    cbn [emit_expression] in Layout. apply layout_append in Layout. destruct Layout as [Left Tail].
    rewrite expression_size in Tail. apply layout_append in Tail. destruct Tail as [Right Binary].
    rewrite expression_size in Binary. cbn [expression_layout] in Binary. destruct Binary as [Binary _].
    exists t. split; [constructor |]. split; [|discriminate].
    eapply core_expression with (root := root) (d := d); eauto.
    eapply continuation_left; eauto. cbn [expression_width] in K.
    replace (pc t + expression_width a + expression_width b + 4)
      with (pc t + (expression_width a + expression_width b + 4)) by lia. exact K.
  - cbn [valid_expression] in Valid. rewrite !andb_true_iff in Valid. destruct Valid as [_ [Va Vb]].
    cbn [emit_expression] in Layout. apply layout_append in Layout. destruct Layout as [Left Tail].
    rewrite expression_size in Tail. apply layout_append in Tail. destruct Tail as [Right Comparison].
    rewrite expression_size in Comparison.
    exists t. split; [constructor |]. split; [|discriminate].
    eapply core_expression with (root := root) (d := d); eauto.
    eapply continuation_compare_left; eauto. rewrite comparison_size.
    destruct op; cbn [expression_width] in K; cbn; repeat rewrite Nat.add_assoc in K; exact K.
  - cbn [valid_expression] in Valid. apply andb_true_iff in Valid. destruct Valid as [_ Va].
    cbn [emit_expression] in Layout. apply layout_append in Layout. destruct Layout as [Left Tail].
    rewrite expression_size in Tail. cbn [expression_layout] in Tail. destruct Tail as [Load _].
    exists t. split; [constructor |]. split; [|discriminate].
    eapply core_expression with (root := root) (d := d); eauto.
    eapply continuation_read; eauto. cbn [expression_width] in K.
    replace (pc t + expression_width a + 3) with (pc t + (expression_width a + 3)) by lia. exact K.
  - cbn [valid_expression] in Valid. apply andb_true_iff in Valid. destruct Valid as [_ Va].
    cbn [emit_expression] in Layout. apply layout_append in Layout. destruct Layout as [Left Tail].
    rewrite expression_size in Tail. cbn [expression_layout] in Tail. destruct Tail as [Alloc _].
    exists t. split; [constructor |]. split; [|discriminate].
    eapply core_expression with (root := root) (d := d); eauto.
    eapply continuation_new; eauto. cbn [expression_width] in K.
    replace (pc t + expression_width a + 3) with (pc t + (expression_width a + 3)) by lia. exact K.
  - cbn [valid_expression] in Valid. rewrite !andb_true_iff in Valid.
    destruct Valid as [UpperF [[LowerF RangeF] Va]].
    cbn [emit_expression] in Layout. apply layout_append in Layout. destruct Layout as [Left Tail].
    rewrite expression_size in Tail. cbn [expression_layout width] in Tail.
    destruct Tail as [Move [Call [Result _]]].
    exists t. split; [constructor |]. split; [|discriminate].
    eapply core_expression with (root := root) (d := d); eauto.
    eapply continuation_argument; eauto.
    + apply Nat.ltb_lt in LowerF, RangeF. lia.
    + replace (pc t + expression_width a + 12) with (pc t + expression_width a + 3 + 9) by lia. exact Result.
    + cbn [expression_width] in K. replace (pc t + expression_width a + 15)
        with (pc t + (expression_width a + 15)) by lia. exact K.
  - destruct (normal_expression fs code depth env Watermark m h (word (N.of_nat h)) m h t d Checked
      (eval_watermark _ _ _ _ _) Ready Bound Valid Layout) as [u [Run Ready1]].
    exists u. split; [exact (proj1 Run) |]. split.
    + rewrite <- (word_idempotent (N.of_nat h)). eapply expression_completion with (t := t) (e := Watermark) (root := root); eauto; lia.
    + intros _. now apply expression_positive in Run.
Qed.

Lemma command_simulation fs code root body p out depth env m h k t :
  verify code = true -> command_code code (address_of fs) root body p out ->
  ready code depth env m h t -> pc t = p -> valid_statement (length fs) body = true ->
  statement_continuation fs code root out k (frames t) ->
  administrative_source (SourceState (Execute body) env m h depth k Running) = true /\
  exists u, steps code t u /\
    core_match fs code
      (match source_step (source_lookup fs) (SourceState (Execute body) env m h depth k Running) with
       | Some next => next | None => SourceState (Execute body) env m h depth k Running end) u.
Proof.
  intros Verified Command Ready Position Valid K.
  destruct Command as [p|n e p Expression Move|e p Expression|a b p Left Right Store|e p Expression Reset|
    a b p middle out Left Right|a b p Left|e yes no p yes_pc out Test Branch Yes No|
    e body p body_pc back_pc end_pc Test Branch Exit Body Back|e p Expression Move Exit].
  - destruct (statement_continuation_resume _ _ _ _ _ _ K)
      as [next [tail [entry [endpoint [Kont [Path [NextValid [NextCode NextK]]]]]]]].
    subst k. split; [reflexivity |].
    destruct Ready as [Machine [Mode Rest]].
    pose proof (jump_path_execution code p entry Verified Path t Machine Mode Position) as Steps.
    exists (at_pc t entry). split; auto.
    eapply core_statement with (root := root) (out := endpoint); eauto.
    eapply ready_at; eauto. unfold ready. tauto.
  - cbn [valid_statement] in Valid. apply andb_true_iff in Valid. destruct Valid as [Local ExpressionValid].
    apply Nat.ltb_lt in Local. split; [reflexivity |]. exists t. split; [constructor |].
    cbn [source_step source_next source_mode source_control continuations locals source_memory source_frontier source_depth].
    eapply core_expression with (root := root) (d := 9); eauto; try lia.
    + now rewrite Position.
    + rewrite Position. eapply continuation_save; eauto.
  - split; [reflexivity |]. exists t. split; [constructor |].
    cbn [source_step source_next source_mode source_control continuations locals source_memory source_frontier source_depth].
    eapply core_expression with (root := root) (d := 9); eauto; try lia.
    + now rewrite Position.
    + rewrite Position. now apply continuation_discard.
  - cbn [valid_statement] in Valid. apply andb_true_iff in Valid. destruct Valid as [LeftValid RightValid].
    split; [reflexivity |]. exists t. split; [constructor |].
    cbn [source_step source_next source_mode source_control continuations locals source_memory source_frontier source_depth].
    eapply core_expression with (root := root) (d := 9); eauto; try lia.
    + now rewrite Position.
    + rewrite Position. eapply continuation_write_address; eauto.
  - split; [reflexivity |]. exists t. split; [constructor |].
    cbn [source_step source_next source_mode source_control continuations locals source_memory source_frontier source_depth].
    eapply core_expression with (root := root) (d := 9); eauto; try lia.
    + now rewrite Position.
    + rewrite Position. eapply continuation_reset; eauto.
  - cbn [valid_statement] in Valid. apply andb_true_iff in Valid. destruct Valid as [LeftValid RightValid].
    split; [reflexivity |]. exists t. split; [constructor |].
    cbn [source_step source_next source_mode source_control continuations locals source_memory source_frontier source_depth].
    eapply core_statement with (root := root) (out := Some middle); eauto.
    + now rewrite Position.
    + eapply continuation_then; eauto.
  - cbn [valid_statement] in Valid. apply andb_true_iff in Valid. destruct Valid as [LeftValid RightValid].
    split; [reflexivity |]. exists t. split; [constructor |].
    cbn [source_step source_next source_mode source_control continuations locals source_memory source_frontier source_depth].
    eapply core_statement with (root := root) (out := None); eauto.
    + now rewrite Position.
    + apply continuation_none. apply continuation_unwind; [reflexivity |].
      now apply statement_continuation_return in K.
  - cbn [valid_statement] in Valid. rewrite !andb_true_iff in Valid.
    destruct Valid as [[TestValid YesValid] NoValid]. split; [reflexivity |]. exists t. split; [constructor |].
    cbn [source_step source_next source_mode source_control continuations locals source_memory source_frontier source_depth].
    eapply core_expression with (root := root) (d := 9); eauto; try lia.
    + now rewrite Position.
    + rewrite Position. eapply continuation_choose; eauto.
  - cbn [valid_statement] in Valid. apply andb_true_iff in Valid. destruct Valid as [TestValid BodyValid].
    assert (Loop : statement_code code (address_of fs) root (While e body) back_pc (Some end_pc)).
    { eapply statement_code_before with (q := p).
      - eapply jump_next; [exact Back | constructor].
      - apply statement_of_command. eapply command_while; eauto. }
    assert (Repeat : statement_code code (address_of fs) root (Sequence body (While e body)) body_pc (Some end_pc)).
    { apply statement_of_command. eapply command_sequence; eauto. }
    assert (Done : statement_code code (address_of fs) root Skip (p + expression_width e + 10) (Some end_pc)).
    { apply statement_code_before with (q := end_pc).
      - eapply jump_next; [exact Exit | constructor].
      - apply statement_of_command. constructor. }
    split; [reflexivity |]. exists t. split; [constructor |].
    cbn [source_step source_next source_mode source_control continuations locals source_memory source_frontier source_depth].
    eapply core_expression with (root := root) (d := 9); eauto; try lia.
    + now rewrite Position.
    + rewrite Position. eapply continuation_choose; eauto.
      cbn [valid_statement]. now rewrite BodyValid, TestValid.
  - split; [reflexivity |]. exists t. split; [constructor |].
    cbn [source_step source_next source_mode source_control continuations locals source_memory source_frontier source_depth].
    eapply core_expression with (root := root) (d := 9); eauto; try lia.
    + now rewrite Position.
    + rewrite Position. eapply continuation_return; eauto.
      now apply statement_continuation_return in K.
Qed.

Lemma statement_simulation fs code depth env body m h k root out t :
  verify code = true -> ready code depth env m h t -> valid_statement (length fs) body = true ->
  statement_code code (address_of fs) root body (pc t) out ->
  statement_continuation fs code root out k (frames t) ->
  administrative_source (SourceState (Execute body) env m h depth k Running) = true /\
  exists u, steps code t u /\
    core_match fs code
      (match source_step (source_lookup fs) (SourceState (Execute body) env m h depth k Running) with
       | Some next => next | None => SourceState (Execute body) env m h depth k Running end) u.
Proof.
  intros Verified Ready Valid Code K.
  inversion Code as [body0 p0 entry actual out0 Path Command Flow]; subst.
  destruct Ready as [Machine [Mode Rest]].
  pose proof (jump_path_execution code (pc t) entry Verified Path t Machine Mode eq_refl) as Steps.
  assert (Ready1 : ready code depth env m h (at_pc t entry)).
  { eapply ready_at; eauto. unfold ready. tauto. }
  pose proof (statement_continuation_flow _ _ _ _ _ _ _ Flow K) as ActualK.
  destruct (command_simulation fs code root body entry actual depth env m h k (at_pc t entry)
    Verified Command Ready1 eq_refl Valid ActualK) as [Administrative [u [Next Match]]].
  split; auto. exists u. split; eauto using steps_trans.
Qed.

Lemma ready_after code depth env m h t u env1 m1 h1 :
  verify code = true -> ready code depth env m h t -> steps code t u ->
  mode u = Running -> length (frames u) = depth -> locals_match env1 (regs u) ->
  mem u = m1 -> frontier u = h1 -> ready code depth env1 m1 h1 u.
Proof.
  intros Verified [Valid Rest] Steps Mode Depth Locals Memory Frontier.
  split; [eapply machine_valid_steps; eauto |]. repeat split; assumption.
Qed.
Lemma value_after fs code depth env m h k root d t u v m1 h1 :
  verify code = true -> ready code depth env m h t -> steps code t u -> mode u = Running ->
  9 <= d < 15 -> regs u d = v -> agrees_below d (regs t) (regs u) ->
  mem u = m1 -> frontier u = h1 -> frames u = frames t ->
  expression_continuation fs code root d (pc u) k (regs t) (frames t) ->
  core_match fs code (SourceState (Value v) env m1 h1 depth k Running) u.
Proof.
  intros Verified Ready Steps Mode Bound Value Below Memory Frontier Stack K.
  destruct Ready as [Valid [Mode0 [Depth [Locals Rest]]]].
  eapply core_value with (root := root) (d := d); eauto.
  - eapply ready_after with (t := t) (env := env) (m := m) (h := h); eauto; try congruence.
    + unfold ready. tauto.
    + eapply locals_agree_below with (d := d); eauto; lia.
  - rewrite Stack. eapply continuation_stable; eassumption.
Qed.
Lemma single_positive code t i : mode t = Running -> decode code (pc t) = Some i ->
  positive_steps code t (execute code t i).
Proof. intros Mode Decoded. eexists. split; [eapply decoded; eauto | constructor]. Qed.
Lemma value_word code depth env m h t d v : ready code depth env m h t -> regs t d = v -> word v = v.
Proof. intros [[Well [Canonical Structural]] Rest] Value. subst v. now apply canonical_register_word. Qed.

Lemma core_to_cek fs code s t : core_match fs code s t -> cek_matches fs code s t.
Proof. intro Match. eapply cek_running; [constructor | exact Match]. Qed.

Lemma continuation_simulation fs code root d p k r stack :
  compilation_check fs code = true -> expression_continuation fs code root d p k r stack ->
  forall depth env m h v,
  ready code depth env m h (State p r m h stack Running) -> 9 <= d < 15 -> r d = v ->
  exists u, steps code (State p r m h stack Running) u /\
    cek_matches fs code
      (match source_step (source_lookup fs) (SourceState (Value v) env m h depth k Running) with
       | Some next => next | None => SourceState (Value v) env m h depth k Running end) u /\
    (administrative_source (SourceState (Value v) env m h depth k Running) = false ->
      positive_steps code (State p r m h stack Running) u).
Proof.
  intros Checked K. pose proof (compilation_verified fs code Checked) as Verified.
  destruct K as [root op b d p k r stack Vb Layout BinDecoded K|
    root op x d p k r stack Lower Left BinDecoded K|
    root op b d p k r stack Vb Layout Comparison K|
    root op x d p k r stack Lower Left Comparison K|
    root d p k r stack LoadDecoded K|root d p k r stack AllocDecoded K|
    root f d p k r stack Range MoveDecoded CallDecoded ResultDecoded K|
    root n p k r stack Local MoveDecoded K|
    root e p k r stack Ve Layout StoreDecoded K|
    root a p k r stack Address StoreDecoded K|
    root p k r stack K|root p k r stack ResetDecoded K|
    root yes no p yes_pc out k r stack BranchDecoded Vy Vn Yes No K|
    root p k r stack MoveDecoded Exit K]; intros depth env m h v Ready Bound Value;
    cbn [source_step source_next source_mode source_control continuations locals source_memory source_frontier source_depth];
    cbn [administrative_source source_control continuations].
  - exists (State p r m h stack Running). split; [constructor |]. split; [apply core_to_cek | discriminate].
    eapply core_expression with (root := root) (d := S d); eauto; cbn; try lia.
    apply continuation_right; eauto; lia.
  - set (t := State p r m h stack Running).
    pose proof (execution_one code t (Binary op d d (S d)) eq_refl BinDecoded) as Steps.
    pose proof (single_positive code t (Binary op d d (S d)) eq_refl BinDecoded) as Positive.
    cbn [t execute regs] in Steps, Positive. rewrite Left, Value in Steps, Positive.
    destruct (eval_bin op x v) as [result|] eqn:Eval.
    + exists (write_reg (at_pc t (p + 4)) d result). split; [exact Steps |]. split; [apply core_to_cek | eauto].
      eapply value_after with (t := t) (root := root) (d := d); eauto; cbn [t write_reg at_pc regs pc mode mem frontier frames]; try reflexivity; try lia.
      * apply put_same.
      * intros n Below. apply put_other. lia.
    + exists (finish t (Fault Division)). split; [exact Steps |]. split; [|eauto].
      eapply cek_fault with (f := Division); reflexivity.
  - exists (State p r m h stack Running). split; [constructor |]. split; [apply core_to_cek | discriminate].
    eapply core_expression with (root := root) (d := S d); eauto; cbn; try lia.
    apply continuation_compare_right; eauto; lia.
  - set (t := State p r m h stack Running).
    set (u := execute_sequence code t (comparison_code op d)).
    pose proof (sequence_execution code (comparison_code op d) t Comparison (comparison_straight op d)) as Steps.
    pose proof (comparison_result code t op d x v eq_refl Left Value) as Result.
    destruct Result as [Mode [Result [Below [Position [Memory [Frontier Stack]]]]]].
    assert (Positive : positive_steps code t u).
    { apply different_positive; auto. intro Equal. change (pc u = p + code_size (comparison_code op d)) in Position.
      rewrite <- Equal in Position. cbn [t pc] in Position. rewrite comparison_size in Position. destruct op; cbn in Position; lia. }
    exists u. split; auto. split; [apply core_to_cek | eauto].
    eapply value_after with (t := t) (root := root) (d := d); eauto; try lia.
    + now rewrite <- compare_word.
    + intros n RangeN. apply Below. lia.
    + unfold u. rewrite Position. exact K.
  - set (t := State p r m h stack Running).
    pose proof (execution_one code t (Load d d) eq_refl LoadDecoded) as Steps.
    pose proof (single_positive code t (Load d d) eq_refl LoadDecoded) as Positive.
    cbn [t execute regs frontier] in Steps, Positive. rewrite Value in Steps, Positive.
    destruct (N.to_nat v + 8 <=? h) eqn:Access.
    + exists (write_reg (at_pc t (p + 3)) d (read64 m (N.to_nat v))). split; [exact Steps |]. split; [apply core_to_cek | eauto].
      eapply value_after with (t := t) (root := root) (d := d); eauto;
        cbn [t write_reg at_pc regs pc mode mem frontier frames]; try reflexivity.
      * apply put_same.
      * intros n Below. apply put_other. lia.
    + exists (finish t (Fault Memory)). split; [exact Steps |]. split; [|eauto].
      eapply cek_fault with (f := Memory); reflexivity.
  - set (t := State p r m h stack Running).
    pose proof (execution_one code t (Alloc d d) eq_refl AllocDecoded) as Steps.
    pose proof (single_positive code t (Alloc d d) eq_refl AllocDecoded) as Positive.
    cbn [t execute regs frontier] in Steps, Positive. rewrite Value in Steps, Positive.
    destruct (h + N.to_nat v <=? memory_size) eqn:Access.
    + exists (write_reg (State (p + 3) r (clear m h (h + N.to_nat v)) (h + N.to_nat v) stack Running) d (N.of_nat h)).
      split; [exact Steps |]. split; [apply core_to_cek | eauto].
      eapply value_after with (t := t) (root := root) (d := d); eauto;
        cbn [t write_reg at_pc regs pc mode mem frontier frames]; try reflexivity.
      * apply put_same.
      * intros n Below. apply put_other. lia.
    + exists (finish t (Fault Memory)). split; [exact Steps |]. split; [|eauto].
      eapply cek_fault with (f := Memory); reflexivity.
  - set (t := State p r m h stack Running).
    assert (Word : word v = v) by (eapply value_word; eauto).
    pose proof (execution_one code t (Move 15 d) eq_refl MoveDecoded) as MoveSteps.
    pose proof (single_positive code t (Move 15 d) eq_refl MoveDecoded) as Positive.
    set (s1 := execute code t (Move 15 d)). fold s1 in MoveSteps, Positive.
    assert (Valid1 : machine_valid code s1) by (eapply machine_valid_steps with (s := t); eauto; exact (proj1 Ready)).
    destruct (checked_call code s1 (address_of fs f) Verified Valid1 CallDecoded) as [Callable Local].
    destruct (nth_error fs f) as [body|] eqn:Found.
    2: { apply nth_error_None in Found. lia. }
    unfold source_lookup. rewrite Found.
    assert (Nonroot : Nat.eqb f 0 = false) by (apply Nat.eqb_neq; lia).
    destruct (checked_function fs code f body Checked Found) as [BodyValid [FunctionLayout FunctionTarget]].
    rewrite Nonroot in FunctionLayout. apply layout_append in FunctionLayout.
    destruct FunctionLayout as [PrologueLayout BodyLayout].
    pose proof (checked_function_code fs code f body Checked Found) as BodyCode. rewrite Nonroot in BodyCode.
    destruct (depth <? stack_size) eqn:Capacity.
    + apply Nat.ltb_lt in Capacity.
      set (s2 := State (address_of fs f) (regs s1) m h
        (Frame (p + 12) (regs s1) :: stack) Running).
      assert (CallEq : execute code s1 (Call (address_of fs f)) = s2).
      { unfold s2. replace (p + 12) with (pc s1 + 9) by (cbn [s1 t execute write_reg at_pc pc width]; lia).
        apply perform_call; auto. change (length stack < stack_size). destruct Ready as [_ [_ [Depth _]]].
        cbn [frames] in Depth. lia. }
      assert (CallSteps : steps code s1 s2) by (rewrite <- CallEq; now apply execution_one).
      pose proof (steps_trans code t s1 s2 MoveSteps CallSteps) as Prefix.
      set (u := execute_sequence code s2 (prologue false)).
      assert (PrologueSteps : steps code s2 u) by (apply sequence_execution; auto using prologue_straight).
      pose proof (steps_trans code t s2 u Prefix PrologueSteps) as Steps.
      assert (Argument : regs s2 15 = word v).
      { cbn [s2 s1 t execute regs write_reg at_pc]. now rewrite put_same, Value. }
      destruct (prologue_result code s2 v eq_refl Argument) as [Mode [Position [Memory [Frontier [Stack Locals]]]]].
      fold u in Mode, Position, Memory, Frontier, Stack, Locals.
      exists u. split; auto. split.
      * apply core_to_cek. eapply core_statement with (root := false) (out := None).
        -- unfold ready. split; [eapply machine_valid_steps with (s := t); eauto; exact (proj1 Ready) |].
           split; [exact Mode |]. split.
           ++ rewrite Stack. cbn [s2 frames length]. destruct Ready as [_ [_ [Depth _]]]. cbn [frames] in Depth. lia.
           ++ split; [exact Locals |]. split; assumption.
        -- exact BodyValid.
        -- rewrite Position. exact BodyCode.
        -- rewrite Stack. apply continuation_none.
           eapply continuation_restore with (caller_root := root) (d := d); eauto.
           ++ eapply local_boundary in Local. replace (p + 12) with (pc s1 + 9) by (cbn [s1 t execute write_reg at_pc pc width]; lia). exact Local.
           ++ eapply locals_agree_below with (d := d); [lia | exact (proj1 (proj2 (proj2 (proj2 Ready)))) |].
              intros n Below. cbn [s1 t execute regs write_reg at_pc]. apply put_other. lia.
           ++ replace (p + 12 + 3) with (p + 15) by lia.
              eapply continuation_stable; [exact K |].
              intros n Below. cbn [s1 t execute regs write_reg at_pc]. apply put_other. lia.
      * intros _. eapply positive_trans; [exact Positive |]. eapply steps_trans; eassumption.
    + apply Nat.ltb_ge in Capacity.
      assert (CallEq : execute code s1 (Call (address_of fs f)) = finish s1 (Fault Stack)).
      { change ((if call_target code (address_of fs f) && local_target code (pc s1) (pc s1 + 9) then
          if length (frames s1) <? stack_size then
            State (address_of fs f) (regs s1) (mem s1) (frontier s1)
              (Frame (pc s1 + 9) (regs s1) :: frames s1) Running
          else finish s1 (Fault Stack)
          else finish s1 (Fault Target)) = finish s1 (Fault Stack)).
        rewrite Callable, Local.
        assert (Full : (length (frames s1) <? stack_size) = false).
        { apply Nat.ltb_ge. change (stack_size <= length stack).
          destruct Ready as [_ [_ [Depth _]]]. cbn [frames] in Depth. lia. }
        now rewrite Full. }
      pose proof (execution_one code s1 (Call (address_of fs f)) eq_refl CallDecoded) as CallSteps.
      rewrite CallEq in CallSteps. exists (finish s1 (Fault Stack)). split; [eapply steps_trans; eassumption |].
      split; [eapply cek_fault with (f := Stack); reflexivity |].
      intros _. eapply positive_trans; eassumption.
  - set (t := State p r m h stack Running).
    assert (Word : word v = v) by (eapply value_word; eauto).
    pose proof (execution_one code t (Move (S n) 9) eq_refl MoveDecoded) as Steps.
    pose proof (single_positive code t (Move (S n) 9) eq_refl MoveDecoded) as Positive.
    set (u := execute code t (Move (S n) 9)). fold u in Steps, Positive.
    exists u. split; auto. split; [apply core_to_cek | eauto].
    eapply core_statement with (root := root) (out := Some (p + 3)); [|reflexivity | |exact K].
    + eapply ready_after with (t := t) (env := env) (m := m) (h := h); eauto; try reflexivity.
      * exact (proj1 (proj2 (proj2 Ready))).
      * cbn [u t execute regs write_reg at_pc]. rewrite Value.
        apply locals_assignment; auto. exact (proj1 (proj2 (proj2 (proj2 Ready)))).
    + apply statement_of_command. constructor.
  - exists (State p r m h stack Running). split; [constructor |]. split; [apply core_to_cek | discriminate].
    eapply core_expression with (root := root) (d := 10); eauto; try lia.
    eapply continuation_write_value; eauto.
  - set (t := State p r m h stack Running).
    pose proof (execution_one code t (Store 9 10) eq_refl StoreDecoded) as Steps.
    pose proof (single_positive code t (Store 9 10) eq_refl StoreDecoded) as Positive.
    cbn [t execute regs frontier] in Steps, Positive. rewrite Address, Value in Steps, Positive.
    destruct (N.to_nat a + 8 <=? h) eqn:Access.
    + exists (State (p + 3) r (write64 m (N.to_nat a) v) h stack Running). split; auto.
      split; [apply core_to_cek | eauto].
      eapply core_statement with (root := root) (out := Some (p + 3)); [|reflexivity | |exact K].
      * eapply ready_after with (t := t) (env := env) (m := m) (h := h); eauto; try reflexivity.
        -- exact (proj1 (proj2 (proj2 Ready))).
        -- exact (proj1 (proj2 (proj2 (proj2 Ready)))).
      * apply statement_of_command. constructor.
    + exists (finish t (Fault Memory)). split; [exact Steps |]. split; [|eauto].
      eapply cek_fault with (f := Memory); reflexivity.
  - exists (State p r m h stack Running). split; [constructor |]. split; [apply core_to_cek | discriminate].
    eapply core_statement with (root := root) (out := Some p); eauto; try reflexivity.
    apply statement_of_command. constructor.
  - set (t := State p r m h stack Running).
    pose proof (execution_one code t (Reset 9) eq_refl ResetDecoded) as Steps.
    pose proof (single_positive code t (Reset 9) eq_refl ResetDecoded) as Positive.
    cbn [t execute regs frontier] in Steps, Positive. rewrite Value in Steps, Positive.
    destruct (N.to_nat v <=? h) eqn:Access.
    + exists (State (p + 2) r m (N.to_nat v) stack Running). split; auto.
      split; [apply core_to_cek | eauto].
      eapply core_statement with (root := root) (out := Some (p + 2)); [|reflexivity | |exact K].
      * eapply ready_after with (t := t) (env := env) (m := m) (h := h); eauto; try reflexivity.
        -- exact (proj1 (proj2 (proj2 Ready))).
        -- exact (proj1 (proj2 (proj2 (proj2 Ready)))).
      * apply statement_of_command. constructor.
    + exists (finish t (Fault Region)). split; [exact Steps |]. split; [|eauto].
      eapply cek_fault with (f := Region); reflexivity.
  - set (t := State p r m h stack Running).
    pose proof (execution_one code t (Branch 9 yes_pc) eq_refl BranchDecoded) as Steps.
    pose proof (single_positive code t (Branch 9 yes_pc) eq_refl BranchDecoded) as Positive.
    pose proof (checked_branch code t 9 yes_pc Verified (proj1 Ready) BranchDecoded) as Guard.
    change (steps code t (if N.eqb (r 9) 0 then at_pc t (p + 10) else
      if local_target code p yes_pc then at_pc t yes_pc else finish t (Fault Target))) in Steps.
    change (positive_steps code t (if N.eqb (r 9) 0 then at_pc t (p + 10) else
      if local_target code p yes_pc then at_pc t yes_pc else finish t (Fault Target))) in Positive.
    change (local_target code p yes_pc = true) in Guard.
    rewrite Value, Guard in Steps, Positive. destruct (N.eqb v 0) eqn:Zero.
    + exists (at_pc t (p + 10)). split; auto. split; [apply core_to_cek | eauto].
      eapply core_statement with (root := root) (out := out); eauto.
      now apply ready_at with (s := t).
    + exists (at_pc t yes_pc). split; auto. split; [apply core_to_cek | eauto].
      eapply core_statement with (root := root) (out := out); eauto.
      now apply ready_at with (s := t).
  - set (t := State p r m h stack Running).
    assert (Word : word v = v) by (eapply value_word; eauto).
    pose proof (execution_one code t (Move 0 9) eq_refl MoveDecoded) as Steps.
    pose proof (single_positive code t (Move 0 9) eq_refl MoveDecoded) as Positive.
    set (u := execute code t (Move 0 9)). fold u in Steps, Positive.
    exists u. split; auto. split; [apply core_to_cek | eauto].
    eapply core_returning with (root := root); eauto.
    + eapply ready_after with (t := t) (env := env) (m := m) (h := h); eauto; try reflexivity.
      * exact (proj1 (proj2 (proj2 Ready))).
      * intros n Local. cbn [u t execute regs write_reg at_pc]. rewrite put_other by lia.
        exact (proj1 (proj2 (proj2 (proj2 Ready))) n Local).
    + cbn [u t execute regs write_reg at_pc]. now rewrite put_same, Value.
Qed.

Lemma returning_simulation fs code root k stack :
  verify code = true -> returning_continuation fs code root k stack ->
  forall depth env m h p r v,
  ready code depth env m h (State p r m h stack Running) -> r 0 = v ->
  decode code p = Some (exit_instruction root) ->
  exists u, steps code (State p r m h stack Running) u /\
    cek_matches fs code
      (match source_step (source_lookup fs) (SourceState (Returning v) env m h depth k Running) with
       | Some next => next | None => SourceState (Returning v) env m h depth k Running end) u /\
    (administrative_source (SourceState (Returning v) env m h depth k Running) = false ->
      positive_steps code (State p r m h stack Running) u).
Proof.
  intros Verified K. destruct K as [|caller_root d return_pc caller k saved stack Bound Boundary MoveDecoded Locals K|
    root item k stack Nonrestore K]; intros depth env m h p r v Ready Value Exit.
  - set (t := State p r m h [] Running).
    exists (finish t Stopped). split; [now apply execution_one with (i := Halt) |]. split.
    + eapply cek_stopped with (value := v); try reflexivity. exact Value.
    + intros _. now apply single_positive with (i := Halt).
  - set (t := State p r m h (Frame return_pc saved :: stack) Running).
    assert (Word : word v = v) by (eapply value_word; eauto).
    set (s1 := State return_pc (put saved 0 v) m h stack Running).
    assert (ReturnEq : execute code t Ret = s1).
    { unfold s1. rewrite <- Value. apply perform_return; auto. }
    assert (ReturnSteps : steps code t s1) by (rewrite <- ReturnEq; now apply execution_one).
    assert (ReturnPositive : positive_steps code t s1) by (rewrite <- ReturnEq; now apply single_positive).
    set (u := execute code s1 (Move d 0)).
    assert (MoveSteps : steps code s1 u) by now apply execution_one.
    pose proof (steps_trans code t s1 u ReturnSteps MoveSteps) as Steps.
    exists u. split; auto. split.
    + apply core_to_cek. cbn [source_step source_mode source_control continuations source_memory source_frontier source_depth].
      eapply core_value with (root := caller_root) (d := d); [|exact Bound | |].
      * unfold ready. split; [eapply machine_valid_steps with (s := t); eauto; exact (proj1 Ready) |].
        split; [reflexivity |]. split.
        -- cbn [u s1 execute write_reg at_pc frames]. destruct Ready as [_ [_ [Depth _]]].
           cbn [frames length] in Depth. lia.
        -- split.
           ++ intros n Local. cbn [u s1 execute write_reg at_pc regs]. rewrite !put_other by lia.
              exact (Locals n Local).
           ++ split; reflexivity.
      * cbn [u s1 execute write_reg at_pc regs]. now rewrite !put_same, !Word.
      * cbn [u s1 execute write_reg at_pc pc frames]. eapply continuation_stable; [exact K |].
        intros n Below. change (put (put saved 0 v) d (word v) n = saved n).
        rewrite !put_other by lia. reflexivity.
    + intros _. eapply positive_trans; eassumption.
  - destruct item; cbn [restore_frame] in Nonrestore; try discriminate;
      cbn [source_step source_next source_mode source_control continuations locals source_memory source_frontier source_depth
        administrative_source restore_frame];
      exists (State p r m h stack Running).
    all: split; [apply steps_refl |].
    all: split; [apply core_to_cek | discriminate].
    all: eapply core_returning with (root := root); eauto.
Qed.

Theorem core_step_simulation fs code s t next :
  compilation_check fs code = true -> core_match fs code s t -> source_step (source_lookup fs) s = Some next ->
  exists u, steps code t u /\ cek_matches fs code next u /\
    (administrative_source s = false -> positive_steps code t u).
Proof.
  intros Checked Match Step. destruct Match as [depth env e m h k t root d Ready Bound Valid Layout K|
    depth env v m h k t root d Ready Bound Value K|
    depth env body m h k t root out Ready Valid Code K|
    depth env v m h k t root Ready Value Exit K].
  - destruct (evaluate_simulation fs code depth env e m h k root d t Checked Ready Bound Valid Layout K)
      as [u [Steps [Match Positive]]]. rewrite Step in Match.
    exists u. repeat split; eauto using core_to_cek.
  - destruct t as [p r m0 h0 stack status].
    destruct Ready as [Machine [Mode [Depth [Locals [Memory Frontier]]]]]. cbn in Mode, Memory, Frontier.
    subst status m0 h0. cbn [regs pc frames] in Value, K.
    destruct (continuation_simulation fs code root d p k r stack Checked K depth env m h v
      ltac:(unfold ready; cbn; tauto) Bound Value) as [u [Steps [Match Positive]]].
    rewrite Step in Match. exists u. repeat split; eauto.
  - destruct (statement_simulation fs code depth env body m h k root out t
      (compilation_verified fs code Checked) Ready Valid Code K) as [Administrative [u [Steps Match]]].
    rewrite Step in Match. exists u. repeat split; eauto using core_to_cek. congruence.
  - destruct t as [p r m0 h0 stack status].
    destruct Ready as [Machine [Mode [Depth [Locals [Memory Frontier]]]]]. cbn in Mode, Memory, Frontier.
    subst status m0 h0. cbn [regs pc frames] in Value, Exit, K.
    destruct (returning_simulation fs code root k stack (compilation_verified fs code Checked) K depth env m h p r v
      ltac:(unfold ready; cbn; tauto) Value Exit) as [u [Steps [Match Positive]]].
    rewrite Step in Match. exists u. repeat split; eauto.
Qed.

Lemma positive_prefix code s t u : steps code s t -> positive_steps code t u -> positive_steps code s u.
Proof.
  intros Steps Positive. induction Steps; auto. exists t. split; auto.
  destruct Positive as [v [Next Rest]]. eapply steps_trans; [exact Steps |].
  eapply steps_cons; eassumption.
Qed.
Theorem cek_step_simulation fs code s t next :
  compilation_check fs code = true -> cek_matches fs code s t -> source_step (source_lookup fs) s = Some next ->
  exists u, steps code t u /\ cek_matches fs code next u /\
    (administrative_source s = false -> positive_steps code t u).
Proof.
  intros Checked Match Step. destruct Match as [s t entry Prefix Core|
    s t value SourceMode Control TargetMode Value Memory Frontier|
    s t f SourceMode TargetMode Memory Frontier].
  - destruct (core_step_simulation fs code s entry next Checked Core Step) as [u [Steps [Next Positive]]].
    exists u. split; [eapply steps_trans; eassumption |]. split; auto.
    intro Computational. eapply positive_prefix; [exact Prefix | now apply Positive].
  - unfold source_step in Step. rewrite SourceMode in Step. discriminate.
  - unfold source_step in Step. rewrite SourceMode in Step. discriminate.
Qed.
Theorem compiler_cek_simulation fs code : compilation_check fs code = true ->
  forward_simulation (source_transition (source_lookup fs)) code (cek_matches fs code).
Proof.
  intro Checked. constructor; [|exact (cek_result fs code)].
  intros s next t Match Step. inversion Step; subst.
  destruct (cek_step_simulation fs code s t next Checked Match H) as [u [Steps [Next Positive]]].
  exists u. auto.
Qed.
Theorem compiler_cek_productive fs code s t next :
  compilation_check fs code = true -> cek_matches fs code s t -> source_step (source_lookup fs) s = Some next ->
  exists u, steps code t u /\ cek_matches fs code next u /\
    (positive_steps code t u \/ source_rank next < source_rank s).
Proof.
  intros Checked Match Step. destruct (cek_step_simulation fs code s t next Checked Match Step)
    as [u [Steps [Next Positive]]]. exists u. repeat split; auto.
  destruct (administrative_source s) eqn:Administrative.
  - right. eapply administrative_rank; eassumption.
  - left. now apply Positive.
Qed.
Theorem compiler_cek_initial fs code main : compilation_check fs code = true -> nth_error fs 0 = Some main ->
  cek_matches fs code (source_initial main) initial.
Proof.
  intros Checked Main. pose proof (compilation_verified fs code Checked) as Verified.
  destruct (checked_function fs code 0 main Checked Main) as [Valid [Layout Address]].
  cbn [Nat.eqb] in Layout, Address. rewrite Address in Layout.
  apply layout_append in Layout. destruct Layout as [Header Body].
  cbn [prologue expression_layout] in Header. destruct Header as [Decoded _].
  pose proof (execution_one code initial Entry eq_refl Decoded) as Steps.
  set (t := execute code initial Entry).
  eapply cek_running with (entry := t); [exact Steps |].
  eapply core_statement with (root := true) (out := None); [|exact Valid | |].
  - unfold ready. split.
    + eapply machine_valid_steps with (s := initial); eauto.
      split; [apply initial_well_formed |]. split; [apply initial_canonical | now apply accepted_initial].
    + split; [reflexivity |]. split; [reflexivity |]. split; [|split; reflexivity].
      intros n Bound. reflexivity.
  - pose proof (checked_function_code fs code 0 main Checked Main) as Code.
    cbn [Nat.eqb] in Code. rewrite Address in Code. exact Code.
  - apply continuation_none. constructor.
Qed.
Theorem compiler_cek_execution fs code s next t :
  compilation_check fs code = true -> source_steps (source_lookup fs) s next -> cek_matches fs code s t ->
  exists u, steps code t u /\ cek_matches fs code next u.
Proof.
  intros Checked Steps. revert t. induction Steps; intros t0 Match.
  - exists t0. split; [constructor | exact Match].
  - inversion H; subst. destruct (cek_step_simulation fs code s t0 t Checked Match H0)
      as [t1 [Prefix [Next Positive]]].
    destruct (IHSteps t1 Next) as [target [Suffix Result]]. exists target. split; eauto using steps_trans.
Qed.
Theorem compiler_cek_termination fs code main final value :
  compilation_check fs code = true -> nth_error fs 0 = Some main ->
  source_steps (source_lookup fs) (source_initial main) final ->
  source_mode final = Stopped -> source_control final = Value value ->
  exists target, steps code initial target /\ mode target = Stopped /\ regs target 0 = value /\
    mem target = source_memory final /\ frontier target = source_frontier final.
Proof.
  intros Checked Main Steps Mode Value.
  destruct (compiler_cek_execution fs code _ _ initial Checked Steps (compiler_cek_initial fs code main Checked Main))
    as [target [Run Match]]. exists target. split; [exact Run |].
  inversion Match; subst.
  - destruct (core_running _ _ _ _ H0). congruence.
  - repeat split; congruence.
  - congruence.
Qed.

Theorem text_forward_simulation chars certs code : compile_text chars certs = Some code ->
  exists fs, check_frontend chars certs = Some fs /\
    forward_simulation (source_transition (source_lookup fs)) code (cek_matches fs code) /\
    (forall main, nth_error fs 0 = Some main -> cek_matches fs code (source_initial main) initial) /\
    (forall s t next, cek_matches fs code s t -> source_step (source_lookup fs) s = Some next ->
      exists u, steps code t u /\ cek_matches fs code next u /\
        (positive_steps code t u \/ source_rank next < source_rank s)).
Proof.
  unfold compile_text. destruct (check_frontend chars certs) as [fs|] eqn:Frontend; try discriminate.
  intro Compile. destruct (compile_bytes_checked fs code Compile) as [Checked Bytes].
  exists fs. split; [reflexivity |]. split; [now apply compiler_cek_simulation |].
  split; [intros main Main; now apply compiler_cek_initial |].
  intros s t next Match Step. eapply compiler_cek_productive; eassumption.
Qed.

Theorem compiler_cek_fault fs code main final f :
  compilation_check fs code = true -> nth_error fs 0 = Some main ->
  source_steps (source_lookup fs) (source_initial main) final -> source_mode final = Fault f ->
  exists target, steps code initial target /\ mode target = Fault f /\
    mem target = source_memory final /\ frontier target = source_frontier final.
Proof.
  intros Checked Main Steps Mode.
  destruct (compiler_cek_execution fs code _ _ initial Checked Steps (compiler_cek_initial fs code main Checked Main))
    as [target [Run Match]]. exists target. split; [exact Run |]. now apply (cek_fault_result fs code final target f Match).
Qed.
Lemma infinite_source_chunk fs code : compilation_check fs code = true ->
  forall s t, cek_matches fs code s t -> source_infinite_steps (source_lookup fs) s ->
  exists next u, source_infinite_steps (source_lookup fs) next /\
    positive_steps code t u /\ cek_matches fs code next u.
Proof.
  intros Checked s. remember (source_rank s) as rank eqn:Rank. revert s Rank.
  induction rank using lt_wf_ind. intros s Rank t Match Infinite.
  inversion Infinite as [s0 next Transition More]; subst s0.
  inversion Transition as [s0 next0 Step]; subst s0 next0.
  destruct (compiler_cek_productive fs code s t next Checked Match Step) as [u [Steps [Next Progress]]].
  destruct Progress as [Positive | Decrease].
  - exists next, u. auto.
  - destruct (H (source_rank next) ltac:(lia) next eq_refl u Next More)
      as [last [target [Forever [Positive Final]]]].
    exists last, target. split; auto. split; auto. eapply positive_prefix; eassumption.
Qed.
Definition pending_infinite fs code t := exists s entry,
  steps code t entry /\ cek_matches fs code s entry /\ source_infinite_steps (source_lookup fs) s.
Lemma pending_infinite_progress fs code t : compilation_check fs code = true -> pending_infinite fs code t ->
  exists u, transition code t u /\ pending_infinite fs code u.
Proof.
  intros Checked [s [entry [Prefix [Match Infinite]]]]. inversion Prefix; subst.
  - destruct (infinite_source_chunk fs code Checked s entry Match Infinite)
      as [next [u [More [[first [Step Rest]] Next]]]].
    exists first. split; auto. exists next, u. auto.
  - exists t0. split; auto. exists s, entry. auto.
Qed.
Theorem compiler_cek_divergence fs code s t : compilation_check fs code = true -> cek_matches fs code s t ->
  source_infinite_steps (source_lookup fs) s -> infinite_steps code t.
Proof.
  intros Checked Match Infinite.
  assert (Pending : pending_infinite fs code t) by (exists s, t; repeat split; auto; constructor).
  clear s Match Infinite. revert t Pending. cofix Forever. intros t Pending.
  destruct (pending_infinite_progress fs code t Checked Pending) as [u [Step Next]].
  eapply infinite_next; [exact Step |]. now apply Forever.
Qed.
