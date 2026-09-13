From Stdlib Require Import List NArith Arith Bool Lia.
From Loosevm Require Import Syntax State Semantics Interpreter Verifier Source.
Import ListNotations.
Fixpoint compile_expression (e : expression) (destination : nat) : option (list instr) :=
  match e with
  | Literal n => Some [Imm destination n]
  | Local x => Some [Move destination (S x)]
  | Operation op a b =>
      match compile_expression a destination, compile_expression b (S destination) with
      | Some lhs, Some rhs => Some (lhs ++ rhs ++ [Binary op destination destination (S destination)])
      | _, _ => None end
  | Compare _ _ _ => None
  | Read a => option_map (fun xs => xs ++ [Load destination destination]) (compile_expression a destination)
  | New n => option_map (fun xs => xs ++ [Alloc destination destination]) (compile_expression n destination)
  | Watermark => Some [Mark destination]
  | Invoke _ _ => None
  end.
Fixpoint execute_sequence code s xs :=
  match xs with
  | [] => s
  | i :: xs => match mode s with
               | Running => execute_sequence code (execute code s i) xs
               | _ => s end end.
Definition compile_assignment (name : nat) (e : expression) :=
  option_map (fun xs => xs ++ [Move (S name) 9]) (compile_expression e 9).
Theorem compile_literal code s d n :
  mode s = Running ->
  regs (execute_sequence code s [Imm d n]) d = word n /\
  pc (execute_sequence code s [Imm d n]) = pc s + 10 /\
  mem (execute_sequence code s [Imm d n]) = mem s /\
  frontier (execute_sequence code s [Imm d n]) = frontier s.
Proof.
  intro M. cbn [execute_sequence]. rewrite M. cbn [execute write_reg at_pc regs pc mem frontier].
  rewrite put_same. auto.
Qed.
Lemma sequence_append code xs ys s :
  execute_sequence code s (xs ++ ys) = execute_sequence code (execute_sequence code s xs) ys.
Proof.
  revert s. induction xs; intro s; cbn; auto.
  destruct (mode s) eqn:M; auto;
  destruct ys; cbn; try rewrite M; auto.
Qed.
Definition expression_layout code start xs :=
  let fix layout p xs :=
      match xs with [] => True | i :: rest => decode code p = Some i /\ layout (p + width i) rest end
  in layout start xs.
Fixpoint variables_below e d : Prop :=
  match e with
  | Literal _ => True
  | Local x => S x < d
  | Operation _ a b => variables_below a d /\ variables_below b d
  | _ => False end.
Fixpoint code_size (xs : list instr) : nat :=
  match xs with [] => 0 | i :: xs => width i + code_size xs end.
Lemma code_size_append xs ys : code_size (xs ++ ys) = code_size xs + code_size ys.
Proof. induction xs; cbn; lia. Qed.
Lemma variables_monotone e d k : variables_below e d -> d <= k -> variables_below e k.
Proof. revert d k. induction e; cbn; intros; try tauto; try lia. firstorder. Qed.
Lemma pure_value_agrees e d (r q : registers) :
  variables_below e d -> (forall n, n < d -> r n = q n) ->
  pure_value (fun x => r (S x)) e = pure_value (fun x => q (S x)) e.
Proof.
  induction e; cbn; intros B E; try reflexivity; try tauto.
  - now rewrite E.
  - destruct B. now rewrite (IHe1 H E), (IHe2 H0 E).
Qed.
Lemma word_idempotent x : word (word x) = word x.
Proof. unfold word. apply N.Div0.mod_mod. Qed.
Lemma pure_value_canonical env e v : pure_value env e = Some v -> word v = v.
Proof.
  revert v. induction e; cbn; intros v H; try discriminate.
  - inversion H; subst. apply word_idempotent.
  - inversion H; subst. apply word_idempotent.
  - destruct (pure_value env e1); try discriminate.
    destruct (pure_value env e2); try discriminate.
    destruct (eval_bin op n n0); inversion H; subst. apply word_idempotent.
Qed.
Definition expression_result s t d v xs :=
  mode t = Running /\ regs t d = word v /\
  (forall n, n < d -> regs t n = regs s n) /\
  pc t = pc s + code_size xs /\ mem t = mem s /\
  frontier t = frontier s /\ frames t = frames s.
Theorem compile_pure_correct code e d xs s v :
  compile_expression e d = Some xs -> variables_below e d ->
  pure_value (fun x => regs s (S x)) e = Some v -> mode s = Running ->
  expression_result s (execute_sequence code s xs) d v xs.
Proof.
  revert d xs s v. induction e; intros d xs s v C B V M; cbn in C, B, V; try contradiction.
  - inversion C; inversion V; subst. unfold expression_result.
    cbn [execute_sequence]. rewrite M. cbn [execute write_reg at_pc mode regs pc mem frontier frames code_size width].
    rewrite put_same, word_idempotent. repeat split; auto; try lia.
    all: try (intros k Hk; apply put_other; lia).
  - inversion C; inversion V; subst. unfold expression_result.
    cbn [execute_sequence]. rewrite M. cbn [execute write_reg at_pc mode regs pc mem frontier frames code_size width].
    rewrite put_same, word_idempotent. repeat split; auto; try lia.
    all: try (intros k Hk; apply put_other; lia).
  - destruct B as [Ba Bb].
    destruct (compile_expression e1 d) as [lhs|] eqn:Cl; try discriminate.
    destruct (compile_expression e2 (S d)) as [rhs|] eqn:Cr; try discriminate.
    inversion C; subst xs.
    destruct (pure_value (fun x => regs s (S x)) e1) as [x|] eqn:Vx; try discriminate.
    destruct (pure_value (fun x => regs s (S x)) e2) as [y|] eqn:Vy; try discriminate.
    destruct (eval_bin op x y) as [z|] eqn:Vz; inversion V; subst v.
    specialize (IHe1 _ _ _ _ Cl Ba Vx M).
    destruct IHe1 as [Ml [Rl [Pl [Pcl [Meml [Fl Sl]]]]]].
    set (s1 := execute_sequence code s lhs) in *.
    assert (Vy1 : pure_value (fun x => regs s1 (S x)) e2 = Some y).
    { rewrite (pure_value_agrees e2 d (regs s1) (regs s) Bb Pl). exact Vy. }
    assert (Bb1 : variables_below e2 (S d)) by (eapply variables_monotone; eauto; lia).
    specialize (IHe2 _ _ _ _ Cr Bb1 Vy1 Ml).
    destruct IHe2 as [Mr [Rr [Pr [Pcr [Memr [Fr Sr]]]]]].
    set (s2 := execute_sequence code s1 rhs) in *.
    rewrite !sequence_append. fold s1 s2.
    cbn [execute_sequence]. rewrite Mr. cbn [execute].
    rewrite (Pr d ltac:(lia)), Rl, Rr.
    rewrite (pure_value_canonical _ _ _ Vx), (pure_value_canonical _ _ _ Vy), Vz.
    unfold expression_result. cbn [write_reg at_pc mode regs pc mem frontier frames].
    rewrite put_same, word_idempotent, !code_size_append.
    cbn [code_size width]. repeat split; auto; try congruence; try lia.
    intros k Hk. rewrite put_other by lia. rewrite Pr by lia. now apply Pl.
Qed.

Definition comparison_code op d :=
  let primary := match op with CSame | CDifferent => Eq | _ => Lt end in
  let args := match op with CAbove | CAtMost => (S d, d) | _ => (d, S d) end in
  [Binary primary d (fst args) (snd args)] ++
  match op with CDifferent | CAtMost | CAtLeast => [Imm (S d) 0%N; Binary Eq d d (S d)] | _ => [] end.
Fixpoint emit_expression (address : nat -> nat) e d : list instr :=
  match e with
  | Literal n => [Imm d (word n)]
  | Local n => [Move d (S n)]
  | Operation op a b => emit_expression address a d ++ emit_expression address b (S d) ++ [Binary op d d (S d)]
  | Compare op a b => emit_expression address a d ++ emit_expression address b (S d) ++ comparison_code op d
  | Read a => emit_expression address a d ++ [Load d d]
  | New a => emit_expression address a d ++ [Alloc d d]
  | Watermark => [Mark d]
  | Invoke f a => emit_expression address a d ++ [Move 15 d; Call (address f); Move d 0]
  end.
Fixpoint expression_width e :=
  match e with
  | Literal _ => 10 | Local _ => 3 | Watermark => 2
  | Operation _ a b => expression_width a + expression_width b + 4
  | Compare op a b => expression_width a + expression_width b +
      match op with CDifferent | CAtMost | CAtLeast => 18 | _ => 4 end
  | Read a | New a => expression_width a + 3
  | Invoke _ a => expression_width a + 15 end.
Fixpoint statement_width s :=
  match s with
  | Skip => 0
  | Assign _ e => expression_width e + 3
  | Discard e => expression_width e
  | Write a b => expression_width a + expression_width b + 3
  | Rewind e => expression_width e + 2
  | Sequence a b => statement_width a + statement_width b
  | Conditional e a b => expression_width e + 19 + statement_width b + statement_width a
  | While e body => expression_width e + 28 + statement_width body
  | Return e => expression_width e + 4 end.
Definition exit_instruction (root : bool) := if root then Halt else Ret.
Fixpoint emit_statement address root s p : list instr :=
  match s with
  | Skip => []
  | Assign n e => emit_expression address e 9 ++ [Move (S n) 9]
  | Discard e => emit_expression address e 9
  | Write a b => emit_expression address a 9 ++ emit_expression address b 10 ++ [Store 9 10]
  | Rewind e => emit_expression address e 9 ++ [Reset 9]
  | Sequence a b => emit_statement address root a p ++ emit_statement address root b (p + statement_width a)
  | Conditional e a b =>
      let no_pc := p + expression_width e + 10 in
      let yes_pc := no_pc + statement_width b + 9 in
      let end_pc := p + statement_width (Conditional e a b) in
      emit_expression address e 9 ++ [Branch 9 yes_pc] ++
      emit_statement address root b no_pc ++ [Jump end_pc] ++ emit_statement address root a yes_pc
  | While e body =>
      let body_pc := p + expression_width e + 19 in
      let end_pc := p + statement_width (While e body) in
      emit_expression address e 9 ++ [Branch 9 body_pc; Jump end_pc] ++
      emit_statement address root body body_pc ++ [Jump p]
  | Return e => emit_expression address e 9 ++ [Move 0 9; exit_instruction root]
  end.
Definition prologue (root : bool) :=
  if root then [Entry] else [Entry; Move 1 15] ++ map (fun r => Imm r 0%N) (seq 2 7).
Definition prologue_width (root : bool) := if root then 1 else 74.
Fixpoint function_addresses fs p root : list nat :=
  match fs with [] => [] | s :: fs => p :: function_addresses fs (p + prologue_width root + statement_width s) false end.
Definition address_of fs n := nth n (function_addresses fs 0 true) 0.
Fixpoint emit_functions address fs p root :=
  match fs with
  | [] => []
  | s :: fs => prologue root ++ emit_statement address root s (p + prologue_width root) ++
      emit_functions address fs (p + prologue_width root + statement_width s) false end.
Definition emit_program fs := emit_functions (address_of fs) fs 0 true.
Fixpoint valid_expression functions e d :=
  (d <? 15) &&
  match e with
  | Literal _ | Watermark => true
  | Local n => n <? 8
  | Operation _ a b | Compare _ a b => valid_expression functions a d && valid_expression functions b (S d)
  | Read a | New a => valid_expression functions a d
  | Invoke f a => (0 <? f) && (f <? functions) && valid_expression functions a d end.
Fixpoint valid_statement functions s :=
  match s with
  | Skip => true
  | Assign n e => (n <? 8) && valid_expression functions e 9
  | Write a b => valid_expression functions a 9 && valid_expression functions b 10
  | Discard e | Rewind e | Return e => valid_expression functions e 9
  | Sequence a b => valid_statement functions a && valid_statement functions b
  | Conditional e a b => valid_expression functions e 9 && valid_statement functions a && valid_statement functions b
  | While e b => valid_expression functions e 9 && valid_statement functions b end.
Definition source_lookup (fs : list statement) n := nth_error fs n.
Definition locals_match env r := forall n, n < 8 -> r (S n) = word (env n).
Lemma expression_size address e d : code_size (emit_expression address e d) = expression_width e.
Proof.
  revert d. induction e; intro d; cbn; rewrite ?code_size_append, ?IHe, ?IHe1, ?IHe2;
  cbn [code_size width]; try lia. destruct op; cbn [comparison_code code_size width]; lia.
Qed.
Lemma statement_size address root s p : code_size (emit_statement address root s p) = statement_width s.
Proof.
  revert p. induction s; intro p; cbn [emit_statement statement_width];
  repeat first [rewrite code_size_append | rewrite expression_size | rewrite IHs1 | rewrite IHs2 | rewrite IHs |
                progress cbn [code_size width]]; try lia.
  unfold exit_instruction. destruct root; cbn [width]; lia.
Qed.
Lemma prologue_size root : code_size (prologue root) = prologue_width root.
Proof. now destruct root. Qed.
Lemma layout_append c p xs ys : expression_layout c p (xs ++ ys) <->
  expression_layout c p xs /\ expression_layout c (p + code_size xs) ys.
Proof.
  revert p. induction xs as [|i xs IH]; intro p.
  - cbn [expression_layout code_size]. rewrite Nat.add_0_r. tauto.
  - change ((decode c p = Some i /\ expression_layout c (p + width i) (xs ++ ys)) <->
            ((decode c p = Some i /\ expression_layout c (p + width i) xs) /\
             expression_layout c (p + (width i + code_size xs)) ys)).
    rewrite IH. replace (p + width i + code_size xs) with (p + (width i + code_size xs)) by lia. tauto.
Qed.

Definition instruction_eq_dec (a b : instr) : {a = b} + {a <> b}.
Proof. decide equality; try apply Nat.eq_dec; try apply N.eq_dec; decide equality. Defined.
Definition instruction_eqb a b := if instruction_eq_dec a b then true else false.
Lemma instruction_eqb_spec a b : instruction_eqb a b = true <-> a = b.
Proof. unfold instruction_eqb. destruct (instruction_eq_dec a b); intuition discriminate. Qed.
Fixpoint layout_check c p xs :=
  match xs with
  | [] => true
  | i :: xs => match decode c p with
               | Some j => instruction_eqb i j && layout_check c (p + width i) xs
               | None => false end
  end.
Lemma layout_check_sound c p xs : layout_check c p xs = true -> expression_layout c p xs.
Proof.
  revert p. induction xs; intro p; cbn [layout_check expression_layout]; auto.
  destruct (decode c p) eqn:D; try discriminate. rewrite andb_true_iff, instruction_eqb_spec.
  intros [I R]. subst. split; [reflexivity | now apply IHxs].
Qed.
Fixpoint guaranteed_return body :=
  match body with
  | Return _ => true
  | Sequence a b => guaranteed_return a || guaranteed_return b
  | Conditional _ a b => guaranteed_return a && guaranteed_return b
  | _ => false end.
Lemma guaranteed_return_sound program body :
  forall depth env m h result env1 m1 h1,
  evaluates_statement program depth env body m h result env1 m1 h1 ->
  guaranteed_return body = true -> exists value, result = Some value.
Proof.
  induction body; intros depth env m h result env1 m1 h1 E G;
    cbn [guaranteed_return] in G; try discriminate.
  - apply orb_true_iff in G. inversion E; subst.
    + destruct G as [Ga | Gb].
      * edestruct IHbody1 as [v V]; eauto. discriminate.
      * eapply IHbody2; eauto.
    + eexists. reflexivity.
  - apply andb_true_iff in G. inversion E; subst; [eapply IHbody1 | eapply IHbody2]; eauto; tauto.
  - inversion E; subst. eexists. reflexivity.
Qed.
Definition function_check fs code f :=
  match nth_error fs f with
  | None => false
  | Some body =>
      let root := Nat.eqb f 0 in
      let p := address_of fs f in
      valid_statement (length fs) body && guaranteed_return body &&
      layout_check code p (prologue root ++ emit_statement (address_of fs) root body (p + prologue_width root)) &&
      (if root then Nat.eqb p 0 else call_target code p)
  end.
Definition compilation_check fs code :=
  negb (Nat.eqb (length fs) 0) && verify code && forallb (function_check fs code) (seq 0 (length fs)).
Lemma checked_function fs code f body :
  compilation_check fs code = true -> nth_error fs f = Some body ->
  valid_statement (length fs) body = true /\
  expression_layout code (address_of fs f)
    (prologue (Nat.eqb f 0) ++ emit_statement (address_of fs) (Nat.eqb f 0) body
      (address_of fs f + prologue_width (Nat.eqb f 0))) /\
  (if Nat.eqb f 0 then address_of fs f = 0 else call_target code (address_of fs f) = true).
Proof.
  unfold compilation_check. rewrite !andb_true_iff. intros [[N V] F] E.
  apply forallb_forall with (x := f) in F.
  - unfold function_check in F. rewrite E in F. rewrite !andb_true_iff in F.
    destruct F as [[[B R] L] P]. split; auto. split; [now apply layout_check_sound |].
    destruct (Nat.eqb f 0); auto. now apply Nat.eqb_eq.
  - apply in_seq. split; [lia |]. apply nth_error_Some. rewrite E. discriminate.
Qed.
Lemma compilation_verified fs code : compilation_check fs code = true -> verify code = true.
Proof. unfold compilation_check. rewrite !andb_true_iff. tauto. Qed.
Lemma compilation_main fs code : compilation_check fs code = true -> exists main, nth_error fs 0 = Some main.
Proof.
  unfold compilation_check. rewrite !andb_true_iff. intros [[N _] _].
  destruct fs; cbn in N; try discriminate. eexists. reflexivity.
Qed.
Theorem evaluations_canonical program :
  (forall depth env e m h v m' h', evaluates_expression program depth env e m h v m' h' -> word v = v) /\
  (forall depth env s m h result env' m' h', evaluates_statement program depth env s m h result env' m' h' ->
     forall v, result = Some v -> word v = v).
Proof.
  apply evaluation_ind; intros; try apply word_idempotent; try discriminate; eauto; congruence.
Qed.
Lemma checked_return fs code f body :
  compilation_check fs code = true -> nth_error fs f = Some body -> guaranteed_return body = true.
Proof.
  unfold compilation_check. rewrite !andb_true_iff. intros [[N V] F] E.
  apply forallb_forall with (x := f) in F.
  - unfold function_check in F. rewrite E in F. rewrite !andb_true_iff in F. tauto.
  - apply in_seq. split; [lia |]. apply nth_error_Some. rewrite E. discriminate.
Qed.
Definition valid_program fs := negb (Nat.eqb (length fs) 0) &&
  forallb (fun body => valid_statement (length fs) body && guaranteed_return body) fs.
