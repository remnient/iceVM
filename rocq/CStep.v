From VST.floyd Require Import proofauto.
From Stdlib Require Import NArith.
From IceVMC Require Import CProgram.
From IceVM Require Import Syntax State Semantics Interpreter CIntegers CRepresentation CState CSpecification CDecoder.
Import ListNotations.
Local Opaque memory_size stack_size.
Definition c_step code s := match step code s with Some t => t | None => s end.
Definition step_spec : ident * funspec :=
 DECLARE _icevm_step
 WITH vm : val, ctx : val, bytes : val, flags : val, owners : val,
      sh : share, code : list nat, s : state
 PRE [tptr (Tstruct _icevm noattr), tptr (Tstruct _icevm_code noattr)]
   PROP () PARAMS (vm; ctx)
   SEP (represents_state vm s; represents_code sh ctx bytes flags owners code)
 POST [tvoid] PROP () RETURN ()
   SEP (represents_state vm (c_step code s); represents_code sh ctx bytes flags owners code).
Definition binary_instruction i := match i with Binary _ _ _ _ => true | _ => false end.
Definition dispatch_value s i :=
  match i with
  | Binary op _ a b => match eval_bin op (regs s a) (regs s b) with Some v => v | None => 0%N end
  | Alloc _ _ => N.of_nat (frontier s)
  | Ret => regs s 0%nat
  | _ => 0%N end.
Definition dispatch_state code s i :=
  let result := execute code s i in
  State (pc s) (if binary_instruction i then regs s else regs result)
    (mem result) (frontier result) (frames result) Running.
Lemma dispatch_writeback code s i : mode (execute code s i) = Running ->
  (if binary_instruction i then
    put (regs (dispatch_state code s i)) (instruction_destination i) (dispatch_value s i)
   else regs (dispatch_state code s i)) = regs (execute code s i).
Proof.
  intro Mode. destruct i; cbn [binary_instruction dispatch_state]; try reflexivity.
  cbn [execute mode] in Mode. unfold dispatch_value, dispatch_state. cbn [binary_instruction execute].
  destruct (eval_bin op (regs s a) (regs s b)); [reflexivity | discriminate].
Qed.
Lemma dispatch_well_formed code s i : well_formed s -> well_formed (dispatch_state code s i).
Proof. intro Well. exact (execute_well_formed code s i Well). Qed.
Lemma dispatch_canonical code s i : canonical s -> canonical (dispatch_state code s i).
Proof.
  intro Canonical. pose proof (execute_canonical code s i Canonical) as Post.
  destruct Canonical as [Registers Rest]. destruct Post as [PostRegisters [Memory Frames]].
  unfold canonical, dispatch_state. cbn [regs mem frames]. destruct (binary_instruction i); tauto.
Qed.
Lemma execution_representation code s i :
  Z.of_nat (length code) <= Int64.max_unsigned ->
  well_formed s -> canonical s -> Z.of_nat (pc s) <= Int64.max_unsigned ->
  Forall (fun f => Z.of_nat (return_pc f) <= Int64.max_unsigned) (frames s) ->
  decode code (pc s) = Some i ->
  well_formed (execute code s i) /\ canonical (execute code s i) /\
  Z.of_nat (pc (execute code s i)) <= Int64.max_unsigned /\
  Forall (fun f => Z.of_nat (return_pc f) <= Int64.max_unsigned) (frames (execute code s i)).
Proof.
  intros Size Well Canonical Position Frames Decoded. pose proof (decode_bounds _ _ _ Decoded) as Bounds.
  split; [now apply execute_well_formed |]. split; [now apply execute_canonical |].
  split; [eapply execute_pc_bounded; eassumption |].
  apply execute_frames_bounded; auto. lia.
Qed.
Definition dispatch_post vm ctx bytes flags owners sh code s i local_i : environ -> mpred :=
  PROP (mode (execute code s i) = Running)
  LOCAL (lvar _i (Tstruct _icevm_instruction noattr) local_i;
    temp _s vm; temp _c ctx;
    temp _next (Vlong (Int64.repr (Z.of_nat (pc (execute code s i)))));
    temp _v (Vlong (cword (dispatch_value s i))))
  SEP (represents_state vm (dispatch_state code s i);
    represents_code sh ctx bytes flags owners code;
    data_at Tsh (Tstruct _icevm_instruction noattr) (instruction_value i) local_i).
Lemma binary_opcode i : binary_instruction i =
  ((16 <=? instruction_opcode i)%nat && (instruction_opcode i <=? 26)%nat)%bool.
Proof. destruct i; try reflexivity. destruct op; reflexivity. Qed.
Local Ltac known_switch :=
  match goal with D : decode _ _ = Some ?instruction |- _ =>
    let key := eval vm_compute in (Z.of_nat (instruction_opcode instruction)) in
    eapply semax_switch_PQR with (n := key);
    [reflexivity | entailer! | entailer!
    |match goal with |- semax _ _ (seq_of_labeled_statement (select_switch ?value ?labels)) _ =>
      let selected := eval vm_compute in (seq_of_labeled_statement (select_switch value labels)) in
      change (seq_of_labeled_statement (select_switch value labels)) with selected;
      repeat apply -> semax_skip_seq
     end]
  end.
Lemma heap_word h : (h <= memory_size)%nat -> 0 <= Z.of_nat h <= Int64.max_unsigned.
Proof.
  intro Bound. apply Nat2Z.inj_le in Bound. change (Z.of_nat h <= 65536) in Bound.
  change (0 <= Z.of_nat h <= 18446744073709551615). lia.
Qed.
Lemma c_address_order h x : (h <= memory_size)%nat -> (x < modulus)%N ->
  Int64.ltu (Int64.repr (Z.of_nat h)) (cword x) = (h <? N.to_nat x)%nat.
Proof.
  intros Heap Canonical. pose proof (heap_word h Heap) as Bound. pose proof (N_nat_Z x) as Position.
  unfold Int64.ltu. rewrite cword_unsigned by exact Canonical.
  rewrite Int64.unsigned_repr by exact Bound.
  destruct (Coqlib.zlt (Z.of_nat h) (Z.of_N x)); destruct (h <? N.to_nat x)%nat eqn:Test;
    try reflexivity; apply Nat.ltb_lt in Test || apply Nat.ltb_ge in Test; exfalso; lia.
Qed.
Lemma c_memory_remainder h x : (h <= memory_size)%nat -> (N.to_nat x <= h)%nat ->
  Int64.ltu (Int64.sub (Int64.repr (Z.of_nat h)) (cword x)) (Int64.repr 8) =
  negb (N.to_nat x + 8 <=? h)%nat.
Proof.
  intros Heap Position. pose proof (heap_word h Heap) as Bound. pose proof (N_nat_Z x) as Address.
  unfold Int64.ltu, cword. rewrite remaining_unsigned by lia.
  rewrite Int64.unsigned_repr by rep_lia.
  destruct (Coqlib.zlt (Z.of_nat h - Z.of_N x) 8);
    destruct (N.to_nat x + 8 <=? h)%nat eqn:Test; cbn [negb]; try reflexivity;
    apply Nat.leb_le in Test || apply Nat.leb_gt in Test; exfalso; lia.
Qed.
Lemma memory_window_value m a : byte_sum (memory_window m a) 8 = Z.of_N (read64 m a).
Proof.
  rewrite <- memory_window_little.
  replace 8%nat with (List.length (memory_window m a)) at 1 by
    (unfold memory_window; rewrite length_map, length_seq; reflexivity).
  apply byte_sum_complete.
Qed.
Definition load_guard_post vm ctx bytes flags owners sh code s d a local_i : environ -> mpred :=
  PROP ()
  LOCAL (temp _t'3 (Val.of_bool (negb (N.to_nat (regs s a) + 8 <=? frontier s)%nat));
    lvar _i (Tstruct _icevm_instruction noattr) local_i;
    temp _s vm; temp _c ctx; temp _address (Vlong (cword (regs s a)));
    temp _next (Vlong (Int64.repr (Z.of_nat (pc s + width (Load d a)))));
    temp _v (Vlong Int64.zero))
  SEP (represents_state vm s; represents_code sh ctx bytes flags owners code;
    data_at Tsh (Tstruct _icevm_instruction noattr) (instruction_value (Load d a)) local_i).
Lemma c_store_shift x n : (x < modulus)%N -> (n < 8)%nat ->
  Int64.shru' (cword x) (Int.mul (Int.repr 8) (Int.repr (Z.of_nat n))) =
  cword (N.shiftr x (N.of_nat (8 * n))).
Proof.
  intros Canonical Bound. unfold Int64.shru'. rewrite c_int_mul_repr.
  rewrite Int.unsigned_repr by rep_lia. rewrite cword_unsigned by exact Canonical.
  unfold cword. rewrite N2Z.inj_shiftr, nat_N_Z, Nat2Z.inj_mul. reflexivity.
Qed.
Lemma c_store_byte x n : (x < modulus)%N -> (n < 8)%nat ->
  Int.zero_ext 8 (Int64.loword (Int64.shru' (cword x) (Int.mul (Int.repr 8) (Int.repr (Z.of_nat n))))) =
  Int.repr (Z.of_N (N.land (N.shiftr x (N.of_nat (8 * n))) 255)).
Proof.
  intros Canonical Bound. rewrite c_store_shift by assumption. apply cword_low_byte.
  pose proof (N.shiftr_upper_bound x (N.of_nat (8 * n))). lia.
Qed.
Lemma c_store_byte_Z x n : (x < modulus)%N -> 0 <= n < 8 ->
  Int.zero_ext 8 (Int64.loword (Int64.shru' (cword x) (Int.mul (Int.repr 8) (Int.repr n)))) =
  Int.repr (Z.of_N (N.land (N.shiftr x (N.of_nat (8 * Z.to_nat n))) 255)).
Proof.
  intros Canonical Bound. replace n with (Z.of_nat (Z.to_nat n)) at 1 by lia.
  apply c_store_byte; [exact Canonical | lia].
Qed.
Lemma c_store_cast64_Z x n : (x < modulus)%N -> 0 <= n < 8 ->
  Int.zero_ext 8 (Int.zero_ext 8
    (Int64.loword (Int64.shru (cword x)
      (Int64.repr (Int.unsigned (Int.mul (Int.repr 8) (Int.repr n))))))) =
  Int.repr (Z.of_N (N.land (N.shiftr x (N.of_nat (8 * Z.to_nat n))) 255)).
Proof.
  intros Canonical Bound. rewrite Int.zero_ext_idem by lia.
  unfold Int64.shru. rewrite Int64.unsigned_repr by
    (pose proof (Int.unsigned_range_2 (Int.mul (Int.repr 8) (Int.repr n)));
     change (0 <= Int.unsigned (Int.mul (Int.repr 8) (Int.repr n)) <= 18446744073709551615); rep_lia).
  fold (Int64.shru' (cword x) (Int.mul (Int.repr 8) (Int.repr n))).
  apply c_store_byte_Z; assumption.
Qed.
Definition store_guard_post vm ctx bytes flags owners sh code s a b local_i : environ -> mpred :=
  PROP ()
  LOCAL (temp _t'5 (Val.of_bool (negb (N.to_nat (regs s a) + 8 <=? frontier s)%nat));
    lvar _i (Tstruct _icevm_instruction noattr) local_i;
    temp _s vm; temp _c ctx; temp _address (Vlong (cword (regs s a)));
    temp _x (Vlong (cword (regs s b)));
    temp _next (Vlong (Int64.repr (Z.of_nat (pc s + width (Store a b)))));
    temp _v (Vlong Int64.zero))
  SEP (represents_state vm s; represents_code sh ctx bytes flags owners code;
    data_at Tsh (Tstruct _icevm_instruction noattr) (instruction_value (Store a b)) local_i).
Lemma c_allocation_test h x : (h <= memory_size)%nat -> (x < modulus)%N ->
  Int64.ltu (Int64.sub (Int64.repr 65536) (Int64.repr (Z.of_nat h))) (cword x) =
  negb (h + N.to_nat x <=? memory_size)%nat.
Proof.
  intros Heap Canonical. pose proof (heap_word h Heap) as Word.
  apply Nat2Z.inj_le in Heap. change (Z.of_nat h <= 65536) in Heap.
  unfold Int64.ltu. rewrite cword_unsigned by exact Canonical.
  rewrite (remaining_unsigned 65536 (Z.of_nat h)) by rep_lia.
  destruct (h + N.to_nat x <=? memory_size)%nat eqn:Test; cbn [negb].
  - apply Nat.leb_le in Test. apply Nat2Z.inj_le in Test.
    change (Z.of_nat (h + N.to_nat x) <= 65536) in Test.
    rewrite Nat2Z.inj_add, N_nat_Z in Test.
    destruct (Coqlib.zlt (65536 - Z.of_nat h) (Z.of_N x)); [exfalso; lia | reflexivity].
  - apply Nat.leb_gt in Test. apply Nat2Z.inj_lt in Test.
    change (65536 < Z.of_nat (h + N.to_nat x)) in Test.
    rewrite Nat2Z.inj_add, N_nat_Z in Test.
    destruct (Coqlib.zlt (65536 - Z.of_nat h) (Z.of_N x)); [reflexivity | exfalso; lia].
Qed.
Lemma c_loop_lt x y : 0 <= x <= 65536 -> 0 <= y <= 65536 ->
  Int64.ltu (Int64.repr x) (Int64.repr y) = (x <? y)%Z.
Proof.
  intros X Y. unfold Int64.ltu. rewrite !Int64.unsigned_repr by rep_lia.
  destruct (Coqlib.zlt x y); destruct (x <? y)%Z eqn:Test; try reflexivity;
    apply Z.ltb_lt in Test || apply Z.ltb_ge in Test; exfalso; lia.
Qed.
Lemma frame_values_top {default : Inhabitant (reptype (Tstruct _icevm_frame noattr))} f fs inactive :
  Znth (Z.of_nat (length fs)) (map frame_value (rev (f :: fs)) ++ inactive) = frame_value f.
Proof.
  rewrite frame_values_pop, Znth_app2 by (rewrite Zlength_map, Zlength_correct, length_rev; lia).
  rewrite Zlength_map, Zlength_correct, length_rev.
  replace (Z.of_nat (length fs) - Z.of_nat (length fs)) with 0 by lia.
  apply Znth_0_cons.
Qed.
Local Ltac return_top f fs inactive :=
  match goal with |- context [Znth ?index (map frame_value ?stack ++ inactive)] =>
    replace index with (Z.of_nat (length fs)) by
      (first [change (Z.of_nat (S (length fs)) - 1 = Z.of_nat (length fs)) |
              change (Z.of_nat (length fs) = Z.of_nat (S (length fs)) - 1)]; lia);
    change (map frame_value stack ++ inactive) with (map frame_value (rev (f :: fs)) ++ inactive);
    rewrite (frame_values_top f fs inactive)
  end.
Lemma body_step : semax_body Vprog Gprog f_icevm_step step_spec.
Proof.
  start_function.
  unfold represents_state, state_fields. Intros inactive.

  forward. forward_if.
  - destruct (mode s) eqn:Mode.
    + contradiction.
    + forward. unfold c_step, step. rewrite Mode.
      unfold represents_state, state_fields. Exists inactive. rewrite Mode. entailer!.
    + forward. unfold c_step, step. rewrite Mode.
      unfold represents_state, state_fields. Exists inactive. rewrite Mode. entailer!.
  - assert (Mode : mode s = Running).
    { destruct (mode s) eqn:Mode; auto; discriminate. }
    forward. unfold represents_code, code_fields. Intros.
    forward_call (sh, ctx, bytes, v_i, code, pc s).
    destruct (decode code (pc s)) as [ins|] eqn:Decoded.
    2: {
      unfold decode_result. forward_if.
      - rewrite Mode. cbn [status_value state_fault]. forward_call (vm, 1, 0, 0). forward.
        unfold c_step, step. rewrite Mode, Decoded.
        unfold represents_state, state_fields. Exists inactive.
        cbn [finish mode pc regs mem frontier frames status_value state_fault fault_number].
        unfold represents_code, code_fields. entailer!.
      - contradiction.
    }
    unfold decode_result. forward_if; [discriminate |].
    pose proof (decode_bounds code (pc s) ins Decoded) as Bounds.
    pose proof (instruction_opcode_bound ins) as OpcodeBound.
    pose proof (decode_registers code (pc s) ins Decoded) as Registers.
    destruct Registers as [Destination [Left Right]].
    unfold instruction_value. forward. forward. forward. forward. forward.
    { entailer!. rewrite register_values_lookup by assumption. exact I. }
    rewrite register_values_lookup by assumption.
    forward. forward.
    { entailer!. rewrite register_values_lookup by assumption. exact I. }
    rewrite register_values_lookup by assumption.
    forward. forward.
    rewrite Int.unsigned_repr by rep_lia. rewrite c_add_repr.
    replace (Z.of_nat (pc s) + Z.of_nat (width ins)) with (Z.of_nat (pc s + width ins)) by lia.
    apply semax_seq with (dispatch_post vm ctx bytes flags owners sh code s ins v_i).
    2: {
      unfold dispatch_post, represents_state. Intros active_padding.
      unfold state_fields. Intros. unfold MORE_COMMANDS, abbreviate, instruction_value.
      forward.
      forward_if (PROP ()
        LOCAL (temp _t'12 (Val.of_bool (binary_instruction ins));
          lvar _i (Tstruct _icevm_instruction noattr) v_i; temp _s vm; temp _c ctx;
          temp _next (Vlong (Int64.repr (Z.of_nat (pc (execute code s ins)))));
          temp _v (Vlong (cword (dispatch_value s ins))))
        SEP (state_fields vm (dispatch_state code s ins) active_padding;
          represents_code sh ctx bytes flags owners code;
          data_at Tsh (Tstruct _icevm_instruction noattr) (instruction_value ins) v_i)).
      1: {
        forward. forward. unfold state_fields, instruction_value. entailer!.
        rewrite binary_opcode.
        assert (Lower : (16 <=? instruction_opcode ins)%nat = true) by (apply Nat.leb_le; lia).
        rewrite Lower. cbn [andb]. unfold Val.of_bool, bool2val.
        destruct (instruction_opcode ins <=? 26)%nat eqn:Upper;
          apply Nat.leb_le in Upper || apply Nat.leb_gt in Upper;
          destruct (zlt 26 (Z.of_nat (instruction_opcode ins))); cbn; try lia; reflexivity.
      }
      1: {
        forward. unfold state_fields, instruction_value. entailer!.
        rewrite binary_opcode.
        assert (Lower : (16 <=? instruction_opcode ins)%nat = false) by (apply Nat.leb_gt; lia).
        rewrite Lower. reflexivity.
      }
      unfold state_fields, instruction_value. Intros.
      forward_if (PROP ()
        LOCAL (lvar _i (Tstruct _icevm_instruction noattr) v_i; temp _s vm; temp _c ctx;
          temp _next (Vlong (Int64.repr (Z.of_nat (pc (execute code s ins))))))
        SEP (state_fields vm (at_pc (execute code s ins) (pc s)) active_padding;
          represents_code sh ctx bytes flags owners code;
          data_at Tsh (Tstruct _icevm_instruction noattr) (instruction_value ins) v_i)).
      1: {
        forward. forward. unfold state_fields, instruction_value.
        rewrite <- register_values_update by assumption.
        pose proof (dispatch_writeback code s ins H9) as Written.
        assert (Binary : binary_instruction ins = true).
        { destruct (binary_instruction ins); auto. unfold typed_true in H15. simpl in H15. discriminate. }
        rewrite Binary in Written. rewrite Written.
        cbn [dispatch_state at_pc pc regs mem frontier frames mode]. entailer!.
      }
      1: {
        forward. unfold state_fields, instruction_value. entailer!.
        assert (Binary : binary_instruction ins = false).
        { destruct (binary_instruction ins); auto. unfold typed_false in H15. simpl in H15. discriminate. }
        unfold dispatch_state. cbn [regs]. rewrite Binary. apply derives_refl.
      }
      unfold state_fields. Intros. forward.
      sep_apply (data_at_data_at_ Tsh (Tstruct _icevm_instruction noattr) (instruction_value ins) v_i).
      unfold c_step, step. rewrite Mode, Decoded.
      unfold represents_state, state_fields. Exists active_padding.
      cbn [at_pc pc regs mem frontier frames mode]. rewrite H9.
      pose proof (execution_representation code s ins
        ltac:(change (Z.of_nat (List.length code) <= 18446744073709551615); lia)
        H0 H1 H2 H3 Decoded) as Represented.
      entailer!. exact (proj1 (proj2 Represented)).
    }
      abbreviate_semax. destruct ins.
      1: {
        known_switch.
        forward.
        sep_apply (data_at_data_at_ Tsh (Tstruct _icevm_instruction noattr) (instruction_value Halt) v_i).
        forward. unfold c_step, step. rewrite Mode, Decoded.
        unfold represents_state, state_fields. Exists inactive.
        cbn [execute finish mode pc regs mem frontier frames status_value state_fault]. try rewrite Mode.
        unfold represents_code, code_fields. entailer!.
      }
      1: {
        known_switch. try rewrite Mode. cbn [status_value state_fault].
        forward_call (vm, 0, 0, 0).
        sep_apply (data_at_data_at_ Tsh (Tstruct _icevm_instruction noattr) (instruction_value Trap) v_i).
        forward. unfold c_step, step. rewrite Mode, Decoded.
        unfold represents_state, state_fields. Exists inactive.
        cbn [execute finish mode pc regs mem frontier frames status_value state_fault fault_number].
        try rewrite Mode. unfold represents_code, code_fields. entailer!.
      }
      1: {
        known_switch. forward. unfold dispatch_post, represents_state, dispatch_state, execute.
        Exists inactive. unfold state_fields.
        cbn [mode pc regs mem frontier frames status_value state_fault dispatch_value binary_instruction].
        try rewrite Mode. unfold represents_code, code_fields. entailer!.
      }
      2: {
        known_switch. forward. unfold dispatch_post, represents_state, dispatch_state, execute.
        Exists inactive. unfold state_fields.
        cbn [mode pc regs mem frontier frames status_value state_fault dispatch_value binary_instruction].
        try rewrite Mode. unfold represents_code, code_fields. entailer!.
      }
      2: {
        known_switch. forward. unfold dispatch_post, represents_state, dispatch_state, execute.
        Exists inactive. unfold state_fields.
        cbn [mode pc regs mem frontier frames status_value state_fault dispatch_value binary_instruction].
        try rewrite Mode. unfold represents_code, code_fields. entailer!.
      }
      2: {
        known_switch. forward. forward. forward. forward.
        unfold dispatch_post, represents_state, dispatch_state, execute.
        Exists inactive. unfold state_fields.
        cbn [mode pc regs mem frontier frames status_value state_fault dispatch_value binary_instruction write_reg at_pc].
        rewrite register_values_update by assumption. try rewrite cword_word.
        try rewrite Mode. unfold represents_code, code_fields. entailer!.
        exact (dispatch_canonical code s (Imm d x) H1).
      }
      2: {
        known_switch. forward. forward. forward.
        unfold dispatch_post, represents_state, dispatch_state, execute.
        Exists inactive. unfold state_fields.
        cbn [mode pc regs mem frontier frames status_value state_fault dispatch_value binary_instruction write_reg at_pc].
        rewrite register_values_update by assumption.
        try rewrite Mode. unfold represents_code, code_fields. entailer!.
        exact (dispatch_canonical code s (Move d a) H1).
      }
      6: {
        known_switch. forward. forward. forward. forward.
        unfold dispatch_post, represents_state, dispatch_state, execute.
        Exists inactive. unfold state_fields.
        cbn [mode pc regs mem frontier frames status_value state_fault dispatch_value binary_instruction write_reg at_pc].
        rewrite register_values_update by assumption.
        try rewrite Mode. unfold represents_code, code_fields. entailer!.
        - exact (dispatch_canonical code s (Mark d) H1).
        - unfold cword. rewrite <- N_nat_Z, Nat2N.id. apply derives_refl.
      }
      2: {
      pose proof (cbinop_correspondence op (regs s a) (regs s b) ((proj1 H1) a) ((proj1 H1) b)) as Arithmetic.
      destruct op.
      1: {
        known_switch. forward. forward.
        cbn [cbinop Datatypes.option_map eval_bin] in Arithmetic. apply (f_equal (fun value : option Int64.int => match value with Some v => v | None => Int64.zero end)) in Arithmetic. cbn [Datatypes.option_map] in Arithmetic.
        unfold dispatch_post, represents_state, dispatch_state, execute.
        cbn [eval_bin]. Exists inactive. unfold state_fields.
        cbn [mode pc regs mem frontier frames status_value state_fault dispatch_value binary_instruction write_reg at_pc eval_bin].
        try rewrite Mode. unfold represents_code, code_fields. rewrite Arithmetic. entailer!.
      }
      1: {
        known_switch. forward. forward.
        cbn [cbinop Datatypes.option_map eval_bin] in Arithmetic. apply (f_equal (fun value : option Int64.int => match value with Some v => v | None => Int64.zero end)) in Arithmetic. cbn [Datatypes.option_map] in Arithmetic.
        unfold dispatch_post, represents_state, dispatch_state, execute.
        cbn [eval_bin]. Exists inactive. unfold state_fields.
        cbn [mode pc regs mem frontier frames status_value state_fault dispatch_value binary_instruction write_reg at_pc eval_bin].
        try rewrite Mode. unfold represents_code, code_fields. rewrite Arithmetic. entailer!.
      }
      1: {
        known_switch. forward. forward.
        cbn [cbinop Datatypes.option_map eval_bin] in Arithmetic. apply (f_equal (fun value : option Int64.int => match value with Some v => v | None => Int64.zero end)) in Arithmetic. cbn [Datatypes.option_map] in Arithmetic.
        unfold dispatch_post, represents_state, dispatch_state, execute.
        cbn [eval_bin]. Exists inactive. unfold state_fields.
        cbn [mode pc regs mem frontier frames status_value state_fault dispatch_value binary_instruction write_reg at_pc eval_bin].
        try rewrite Mode. unfold represents_code, code_fields. rewrite Arithmetic. entailer!.
      }
      2: {
        known_switch. forward. forward.
        cbn [cbinop Datatypes.option_map eval_bin] in Arithmetic. apply (f_equal (fun value : option Int64.int => match value with Some v => v | None => Int64.zero end)) in Arithmetic. cbn [Datatypes.option_map] in Arithmetic.
        unfold dispatch_post, represents_state, dispatch_state, execute.
        cbn [eval_bin]. Exists inactive. unfold state_fields.
        cbn [mode pc regs mem frontier frames status_value state_fault dispatch_value binary_instruction write_reg at_pc eval_bin].
        try rewrite Mode. unfold represents_code, code_fields. rewrite Arithmetic. entailer!.
      }
      2: {
        known_switch. forward. forward.
        cbn [cbinop Datatypes.option_map eval_bin] in Arithmetic. apply (f_equal (fun value : option Int64.int => match value with Some v => v | None => Int64.zero end)) in Arithmetic. cbn [Datatypes.option_map] in Arithmetic.
        unfold dispatch_post, represents_state, dispatch_state, execute.
        cbn [eval_bin]. Exists inactive. unfold state_fields.
        cbn [mode pc regs mem frontier frames status_value state_fault dispatch_value binary_instruction write_reg at_pc eval_bin].
        try rewrite Mode. unfold represents_code, code_fields. rewrite Arithmetic. entailer!.
      }
      2: {
        known_switch. forward. forward.
        cbn [cbinop Datatypes.option_map eval_bin] in Arithmetic. apply (f_equal (fun value : option Int64.int => match value with Some v => v | None => Int64.zero end)) in Arithmetic. cbn [Datatypes.option_map] in Arithmetic.
        unfold dispatch_post, represents_state, dispatch_state, execute.
        cbn [eval_bin]. Exists inactive. unfold state_fields.
        cbn [mode pc regs mem frontier frames status_value state_fault dispatch_value binary_instruction write_reg at_pc eval_bin].
        try rewrite Mode. unfold represents_code, code_fields. rewrite Arithmetic. entailer!.
      }
      1: {
        known_switch. forward_if.
        - assert (Zero : regs s b = 0%N).
          { apply (f_equal Int64.unsigned) in H9.
            rewrite cword_unsigned in H9 by exact ((proj1 H1) b).
            rewrite Int64.unsigned_zero in H9. lia. }
          rewrite Mode. cbn [status_value state_fault]. forward_call (vm, 6, 0, 0).
          sep_apply (data_at_data_at_ Tsh (Tstruct _icevm_instruction noattr) (instruction_value (Binary Div d a b)) v_i).
          forward. unfold c_step, step. rewrite Mode, Decoded.
          cbn [execute eval_bin]. rewrite Zero. cbn [N.eqb].
          unfold represents_state, state_fields. Exists inactive.
          cbn [finish mode pc regs mem frontier frames status_value state_fault fault_number].
          try rewrite Mode. unfold represents_code, code_fields. entailer!.
        - assert (Nonzero : N.eqb (regs s b) 0 = false).
          { apply N.eqb_neq. intro Zero. rewrite Zero in H9. contradiction H9. reflexivity. }
          forward. forward.
          cbn [cbinop Datatypes.option_map eval_bin] in Arithmetic. rewrite Nonzero in Arithmetic.
          assert (NonzeroC : Int64.eq (cword (regs s b)) Int64.zero = false).
          { change Int64.zero with (cword 0%N). rewrite cword_eq by (try exact ((proj1 H1) b); reflexivity). exact Nonzero. }
          rewrite NonzeroC in Arithmetic.
          apply (f_equal (fun value : option Int64.int => match value with Some v => v | None => Int64.zero end)) in Arithmetic.
          cbn [Datatypes.option_map] in Arithmetic.
          unfold dispatch_post, represents_state, dispatch_state, execute.
          cbn [eval_bin]. rewrite Nonzero. Exists inactive. unfold state_fields.
          cbn [mode pc regs mem frontier frames status_value state_fault dispatch_value binary_instruction write_reg at_pc eval_bin].
          rewrite Nonzero. try rewrite Mode. unfold represents_code, code_fields. rewrite Arithmetic. entailer!.
      }
      1: {
        known_switch. forward.
        { entailer!. change (Int64.unsigned (Int64.and (cword (regs s b)) (Int64.repr 63)) < 64).
          rewrite cword_mask by exact ((proj1 H1) b).
          rewrite cword_unsigned by (pose proof (N.land_le_r (regs s b) 63); unfold modulus; lia).
          pose proof (N.land_le_r (regs s b) 63). lia. }
        forward.
        cbn [cbinop Datatypes.option_map eval_bin] in Arithmetic. apply (f_equal (fun value : option Int64.int => match value with Some v => v | None => Int64.zero end)) in Arithmetic. cbn [Datatypes.option_map] in Arithmetic.
        unfold dispatch_post, represents_state, dispatch_state, execute.
        cbn [eval_bin]. Exists inactive. unfold state_fields.
        cbn [mode pc regs mem frontier frames status_value state_fault dispatch_value binary_instruction write_reg at_pc eval_bin].
        try rewrite Mode. unfold represents_code, code_fields. rewrite Arithmetic. entailer!.
      }
      1: {
        known_switch. forward.
        { entailer!. change (Int64.unsigned (Int64.and (cword (regs s b)) (Int64.repr 63)) < 64).
          rewrite cword_mask by exact ((proj1 H1) b).
          rewrite cword_unsigned by (pose proof (N.land_le_r (regs s b) 63); unfold modulus; lia).
          pose proof (N.land_le_r (regs s b) 63). lia. }
        forward.
        cbn [cbinop Datatypes.option_map eval_bin] in Arithmetic. apply (f_equal (fun value : option Int64.int => match value with Some v => v | None => Int64.zero end)) in Arithmetic. cbn [Datatypes.option_map] in Arithmetic.
        unfold dispatch_post, represents_state, dispatch_state, execute.
        cbn [eval_bin]. Exists inactive. unfold state_fields.
        cbn [mode pc regs mem frontier frames status_value state_fault dispatch_value binary_instruction write_reg at_pc eval_bin].
        try rewrite Mode. unfold represents_code, code_fields. rewrite Arithmetic. entailer!.
      }
      1: {
        known_switch. forward. forward.
        cbn [cbinop Datatypes.option_map eval_bin] in Arithmetic. apply (f_equal (fun value : option Int64.int => match value with Some v => v | None => Int64.zero end)) in Arithmetic. cbn [Datatypes.option_map] in Arithmetic.
        unfold dispatch_post, represents_state, dispatch_state, execute.
        cbn [eval_bin]. Exists inactive. unfold state_fields.
        cbn [mode pc regs mem frontier frames status_value state_fault dispatch_value binary_instruction write_reg at_pc eval_bin].
        try rewrite Mode. unfold represents_code, code_fields. rewrite Arithmetic. cbn [instruction_left instruction_right]. unfold Int64.eq, Int64.cmpu. destruct (Coqlib.zeq (Int64.unsigned (cword (regs s a))) (Int64.unsigned (cword (regs s b)))) eqn:Comparison; entailer!; cbn [instruction_left instruction_right]; unfold Int64.eq; rewrite Comparison; reflexivity.
      }
      1: {
        known_switch. forward. forward.
        cbn [cbinop Datatypes.option_map eval_bin] in Arithmetic. apply (f_equal (fun value : option Int64.int => match value with Some v => v | None => Int64.zero end)) in Arithmetic. cbn [Datatypes.option_map] in Arithmetic.
        unfold dispatch_post, represents_state, dispatch_state, execute.
        cbn [eval_bin]. Exists inactive. unfold state_fields.
        cbn [mode pc regs mem frontier frames status_value state_fault dispatch_value binary_instruction write_reg at_pc eval_bin].
        try rewrite Mode. unfold represents_code, code_fields. rewrite Arithmetic. cbn [instruction_left instruction_right]. unfold Int64.ltu, Int64.cmpu. destruct (Coqlib.zlt (Int64.unsigned (cword (regs s a))) (Int64.unsigned (cword (regs s b)))) eqn:Comparison; entailer!; cbn [instruction_left instruction_right]; unfold Int64.ltu; rewrite Comparison; reflexivity.
      }
      }
      6: {
      known_switch. forward. forward.
      pose proof (decode_encodable _ _ _ H6 Decoded) as Encodable.
      cbn [Encoding.encodable] in Encodable. apply N.ltb_lt in Encodable.
      apply N2Z.inj_lt in Encodable. rewrite nat_N_Z in Encodable.
      change (Z.of_nat target < 18446744073709551616) in Encodable.
      assert (TargetBound : Z.of_nat target <= Int64.max_unsigned).
      { change (Z.of_nat target <= 18446744073709551615). lia. }
      forward_call (sh, ctx, bytes, flags, owners, code, pc s, target).
      { unfold represents_code, code_fields. entailer!. cbn [instruction_immediate]. unfold cword. rewrite nat_N_Z. reflexivity. }
      { unfold represents_code, code_fields. entailer!. }
      forward_if.
      + assert (Gate : local_target code (pc s) target = false) by
          (destruct (local_target code (pc s) target); auto; discriminate).
        rewrite Mode. cbn [status_value state_fault]. forward_call (vm, 2, 0, 0).
        sep_apply (data_at_data_at_ Tsh (Tstruct _icevm_instruction noattr) (instruction_value (Jump target)) v_i).
        forward. unfold c_step, step. rewrite Mode, Decoded. cbn [execute]. unfold transfer. rewrite Gate.
        unfold represents_state, state_fields. Exists inactive.
        cbn [finish mode pc regs mem frontier frames status_value state_fault fault_number].
        try rewrite Mode. unfold represents_code, code_fields. entailer!.
      + assert (Gate : local_target code (pc s) target = true) by
          (destruct (local_target code (pc s) target); auto; congruence).
        forward. unfold dispatch_post, represents_state, dispatch_state, execute, transfer. rewrite Gate.
        Exists inactive. unfold state_fields.
        cbn [mode pc regs mem frontier frames status_value state_fault dispatch_value binary_instruction at_pc].
        try rewrite Mode. unfold represents_code, code_fields. entailer!.
        cbn [instruction_immediate]. unfold cword. rewrite nat_N_Z. reflexivity.
      }
      6: {
      known_switch. forward. forward.
      { entailer!. rewrite register_values_lookup by assumption. exact I. }
      rewrite register_values_lookup by assumption. forward_if.
      1: {
        assert (Zero : regs s a = 0%N).
        { apply (f_equal Int64.unsigned) in H9.
          rewrite cword_unsigned in H9 by exact ((proj1 H1) a).
          rewrite Int64.unsigned_zero in H9. lia. }
        assert (Test : N.eqb (regs s a) 0 = true) by (apply N.eqb_eq; exact Zero).
        forward. unfold dispatch_post, represents_state, dispatch_state, execute. rewrite Test.
        Exists inactive. unfold state_fields.
        cbn [mode pc regs mem frontier frames status_value state_fault dispatch_value binary_instruction at_pc].
        try rewrite Mode. unfold represents_code, code_fields. entailer!.
      }
      1: {
        assert (Nonzero : N.eqb (regs s a) 0 = false).
        { apply N.eqb_neq. intro Zero. rewrite Zero in H9. contradiction H9. reflexivity. }
        forward. forward.
      pose proof (decode_encodable _ _ _ H6 Decoded) as Encodable.
      cbn [Encoding.encodable] in Encodable. apply andb_true_iff in Encodable. destruct Encodable as [_ Encodable]. apply N.ltb_lt in Encodable.
      apply N2Z.inj_lt in Encodable. rewrite nat_N_Z in Encodable.
      change (Z.of_nat target < 18446744073709551616) in Encodable.
      assert (TargetBound : Z.of_nat target <= Int64.max_unsigned).
      { change (Z.of_nat target <= 18446744073709551615). lia. }
      forward_call (sh, ctx, bytes, flags, owners, code, pc s, target).
      { unfold represents_code, code_fields. entailer!. cbn [instruction_immediate]. unfold cword. rewrite nat_N_Z. reflexivity. }
      { unfold represents_code, code_fields. entailer!. }
      forward_if.
        1: { assert (Gate : local_target code (pc s) target = false) by
          (destruct (local_target code (pc s) target); auto; discriminate).
        rewrite Mode. cbn [status_value state_fault]. forward_call (vm, 2, 0, 0).
        sep_apply (data_at_data_at_ Tsh (Tstruct _icevm_instruction noattr) (instruction_value (Branch a target)) v_i).
        forward. unfold c_step, step. rewrite Mode, Decoded. cbn [execute]. rewrite Nonzero. unfold transfer. rewrite Gate.
        unfold represents_state, state_fields. Exists inactive.
        cbn [finish mode pc regs mem frontier frames status_value state_fault fault_number].
        try rewrite Mode. unfold represents_code, code_fields. entailer!.
        }
        1: { assert (Gate : local_target code (pc s) target = true) by
          (destruct (local_target code (pc s) target); auto; congruence).
        forward. unfold dispatch_post, represents_state, dispatch_state, execute, transfer. rewrite Nonzero, Gate.
        Exists inactive. unfold state_fields.
        cbn [mode pc regs mem frontier frames status_value state_fault dispatch_value binary_instruction at_pc].
        try rewrite Mode. unfold represents_code, code_fields. entailer!.
        cbn [instruction_immediate]. unfold cword. rewrite nat_N_Z. reflexivity.
        }
      }
      }
      6: {
      known_switch. forward. forward.
      { entailer!. rewrite register_values_lookup by assumption. exact I. }
      rewrite register_values_lookup by assumption. forward.
      assert (TargetBound : Z.of_nat (N.to_nat (regs s a)) <= Int64.max_unsigned).
      { rewrite N_nat_Z. pose proof ((proj1 H1) a) as Bound. apply N2Z.inj_lt in Bound.
        change (Z.of_N (regs s a) < 18446744073709551616) in Bound.
        change (Z.of_N (regs s a) <= 18446744073709551615). lia. }
      forward_call (sh, ctx, bytes, flags, owners, code, pc s, (N.to_nat (regs s a))).
      { unfold represents_code, code_fields. entailer!. unfold cword. rewrite N_nat_Z. reflexivity. }
      { unfold represents_code, code_fields. entailer!. }
      forward_if.
      + assert (Gate : local_target code (pc s) (N.to_nat (regs s a)) = false) by
          (destruct (local_target code (pc s) (N.to_nat (regs s a))); auto; discriminate).
        rewrite Mode. cbn [status_value state_fault]. forward_call (vm, 2, 0, 0).
        sep_apply (data_at_data_at_ Tsh (Tstruct _icevm_instruction noattr) (instruction_value (Indirect a)) v_i).
        forward. unfold c_step, step. rewrite Mode, Decoded. cbn [execute]. unfold transfer. rewrite Gate.
        unfold represents_state, state_fields. Exists inactive.
        cbn [finish mode pc regs mem frontier frames status_value state_fault fault_number].
        try rewrite Mode. unfold represents_code, code_fields. entailer!.
      + assert (Gate : local_target code (pc s) (N.to_nat (regs s a)) = true) by
          (destruct (local_target code (pc s) (N.to_nat (regs s a))); auto; congruence).
        forward. unfold dispatch_post, represents_state, dispatch_state, execute, transfer. rewrite Gate.
        Exists inactive. unfold state_fields.
        cbn [mode pc regs mem frontier frames status_value state_fault dispatch_value binary_instruction at_pc].
        try rewrite Mode. unfold represents_code, code_fields. entailer!.
        unfold cword. rewrite N_nat_Z. reflexivity.
      }
      5: {
      known_switch. forward. forward.
      { entailer!. rewrite register_values_lookup by assumption. exact I. }
      rewrite register_values_lookup by assumption. forward.
      assert (HeapBound : Z.of_nat (frontier s) <= 65536).
      { pose proof (proj1 H0) as Bound. apply Nat2Z.inj_le in Bound. change (Z.of_nat (frontier s) <= 65536) in Bound. exact Bound. }
      assert (HeapWord : 0 <= Z.of_nat (frontier s) <= Int64.max_unsigned).
      { change (0 <= Z.of_nat (frontier s) <= 18446744073709551615). lia. }
      forward_if.
      1: {
        assert (Test : (N.to_nat (regs s a) <=? frontier s)%nat = false).
        { apply Nat.leb_gt. unfold Int64.ltu in H9. rewrite cword_unsigned in H9 by exact ((proj1 H1) a).
          rewrite Int64.unsigned_repr in H9 by exact HeapWord. pose proof (N_nat_Z (regs s a)). destruct (Coqlib.zlt (Z.of_nat (frontier s)) (Z.of_N (regs s a))); try discriminate; lia. }
        rewrite Mode. cbn [status_value state_fault]. forward_call (vm, 4, 0, 0).
        sep_apply (data_at_data_at_ Tsh (Tstruct _icevm_instruction noattr) (instruction_value (Reset a)) v_i).
        forward. unfold c_step, step. rewrite Mode, Decoded. cbn [execute]. rewrite Test.
        unfold represents_state, state_fields. Exists inactive.
        cbn [finish mode pc regs mem frontier frames status_value state_fault fault_number].
        try rewrite Mode. unfold represents_code, code_fields. entailer!.
      }
      1: {
        assert (Test : (N.to_nat (regs s a) <=? frontier s)%nat = true).
        { apply Nat.leb_le. unfold Int64.ltu in H9. rewrite cword_unsigned in H9 by exact ((proj1 H1) a).
          rewrite Int64.unsigned_repr in H9 by exact HeapWord. pose proof (N_nat_Z (regs s a)). destruct (Coqlib.zlt (Z.of_nat (frontier s)) (Z.of_N (regs s a))); try discriminate; lia. }
        forward. forward.
        { entailer!. rewrite register_values_lookup by assumption. exact I. }
        rewrite register_values_lookup by assumption. forward. forward.
        unfold dispatch_post, represents_state, dispatch_state, execute. rewrite Test.
        Exists inactive. unfold state_fields.
        cbn [mode pc regs mem frontier frames status_value state_fault dispatch_value binary_instruction at_pc].
        try rewrite Mode. unfold represents_code, code_fields. entailer!.
        - split.
          + apply Nat.leb_le in Test. eapply Nat.le_trans; [exact Test | exact (proj1 H0)].
          + exact (proj2 H0).
        - unfold cword. rewrite N_nat_Z. apply derives_refl.
      }
      }
      2: {
      known_switch. forward. forward.
      pose proof (heap_word (frontier s) (proj1 H0)) as HeapWord.
      pose proof (c_address_order (frontier s) (regs s a) (proj1 H0) ((proj1 H1) a)) as Order.
      forward_if (load_guard_post vm ctx bytes flags owners sh code s d a v_i).
      1: {
        cbn [instruction_left] in H9. rewrite Order in H9. apply Nat.ltb_lt in H9.
        assert (Access : (N.to_nat (regs s a) + 8 <=? frontier s)%nat = false) by
          (apply Nat.leb_gt; lia).
        forward. unfold load_guard_post, represents_state, state_fields, represents_code, code_fields.
        Exists inactive. rewrite Access. cbn [negb Val.of_bool]. entailer!.
      }
      1: {
        cbn [instruction_left] in H9. rewrite Order in H9. apply Nat.ltb_ge in H9.
        forward. forward.
        unfold load_guard_post, represents_state, state_fields, represents_code, code_fields.
        Exists inactive.
        rewrite <- (c_memory_remainder (frontier s) (regs s a) (proj1 H0) H9).
        cbn [instruction_left]. entailer!.
        change (Val.of_bool (Int64.ltu (Int64.sub (Int64.repr (Z.of_nat (frontier s))) (cword (regs s a))) (Int64.repr 8)) =
          bool2val (Int64.ltu (Int64.sub (Int64.repr (Z.of_nat (frontier s))) (cword (regs s a))) (Int64.repr 8))).
        destruct (Int64.ltu (Int64.sub (Int64.repr (Z.of_nat (frontier s))) (cword (regs s a))) (Int64.repr 8)); reflexivity.
      }
      unfold load_guard_post, represents_state, state_fields. Intros inactive_after. Intros.
      forward_if.
      1: {
        assert (Access : (N.to_nat (regs s a) + 8 <=? frontier s)%nat = false).
        { destruct (N.to_nat (regs s a) + 8 <=? frontier s)%nat; auto.
          match goal with H : typed_true _ _ |- _ => unfold typed_true in H; simpl in H; discriminate end. }
        rewrite Mode. cbn [status_value state_fault]. forward_call (vm, 3, 0, 0).
        sep_apply (data_at_data_at_ Tsh (Tstruct _icevm_instruction noattr) (instruction_value (Load d a)) v_i).
        forward. unfold c_step, step. rewrite Mode, Decoded. cbn [execute]. rewrite Access.
        unfold represents_state, state_fields. Exists inactive_after.
        cbn [finish mode pc regs mem frontier frames status_value state_fault fault_number].
        try rewrite Mode. unfold represents_code, code_fields. entailer!.
      }
      1: {
        assert (Access : (N.to_nat (regs s a) + 8 <=? frontier s)%nat = true).
        { destruct (N.to_nat (regs s a) + 8 <=? frontier s)%nat; auto.
          match goal with H : typed_false _ _ |- _ => unfold typed_false in H; simpl in H; discriminate end. }
        apply Nat.leb_le in Access.
        assert (Position : (N.to_nat (regs s a) + 8 <= memory_size)%nat) by
          (eapply Nat.le_trans; [exact Access | exact (proj1 H0)]).
        assert (ZPosition : Z.of_nat (N.to_nat (regs s a)) + 8 <= 65536).
        { pose proof Position as Bound. apply Nat2Z.inj_le in Bound.
          change (Z.of_nat (N.to_nat (regs s a) + 8) <= 65536) in Bound. lia. }
        assert_PROP (isptr vm) as Pointer by entailer!.
        destruct vm as [|vmint|vmlong|vmfloat|vmsingle|block offset]; try contradiction.
        assert_PROP (field_compatible (Tstruct _icevm noattr) [StructField _memory] (Vptr block offset)) as MemoryField by entailer!.
        pose proof (field_compatible_shrink (Tstruct _icevm noattr) [StructField _memory] [] (Vptr block offset) MemoryField) as Parent.
        rewrite (field_at_data_at Tsh (Tstruct _icevm noattr) [StructField _memory]).
        change (nested_field_type (Tstruct _icevm noattr) [StructField _memory]) with (tarray tuchar 65536).
        set (base := field_address (Tstruct _icevm noattr) [StructField _memory] (Vptr block offset)).
        assert_PROP (field_compatible (tarray tuchar 65536) [] base) as Array by entailer!.
        rewrite (byte_window_split Tsh 65536 (memory_values (mem s)) base (Z.of_nat (N.to_nat (regs s a))))
          by (rewrite ?memory_values_length; lia).
        replace (Z.of_nat (N.to_nat (regs s a)) + 8) with (Z.of_nat (N.to_nat (regs s a) + 8)) by lia.
        rewrite memory_values_window by exact Position.
        forward_call (field_address0 (tarray tuchar 65536) [ArraySubsc (Z.of_nat (N.to_nat (regs s a)))] base,
          Tsh, memory_window (mem s) (N.to_nat (regs s a))).
        1: {
          entailer!. rewrite field_address0_offset by auto with field_compatible.
          unfold base. rewrite field_address_offset by auto with field_compatible.
          cbn [nested_field_offset nested_field_rec nested_field_type tarray tuchar sizeof offset_val].
          unfold Ptrofs.of_int64. rewrite cword_unsigned by exact ((proj1 H1) a).
          rewrite <- N_nat_Z. autorewrite with norm. reflexivity.
        }
        1: { cancel. }
        1: {
          apply memory_window_bytes. exact (proj1 (proj2 H1)).
        }
        rewrite <- memory_values_window by exact Position.
        replace (Z.of_nat (N.to_nat (regs s a) + 8)) with (Z.of_nat (N.to_nat (regs s a)) + 8) by lia.
        sep_apply (byte_window_join Tsh 65536 (memory_values (mem s)) base (Z.of_nat (N.to_nat (regs s a)))
          ltac:(lia) ltac:(lia) ltac:(apply memory_values_length)).
        unfold base.
        rewrite memory_window_value.
        fold (cword (read64 (mem s) (N.to_nat (regs s a)))).
        unfold instruction_value. forward. forward. forward.
        assert (Test : (N.to_nat (regs s a) + 8 <=? frontier s)%nat = true) by
          (apply Nat.leb_le; exact Access).
        pose proof (dispatch_canonical code s (Load d a) H1) as Canonical.
        unfold dispatch_state, execute in Canonical. rewrite Test in Canonical.
        unfold dispatch_post, represents_state, dispatch_state, execute. rewrite Test.
        Exists inactive_after. unfold state_fields.
        cbn [mode pc regs mem frontier frames status_value state_fault dispatch_value binary_instruction write_reg at_pc].
        rewrite register_values_update by assumption.
        try rewrite Mode. unfold represents_code, code_fields.
        rewrite (field_at_data_at Tsh (Tstruct _icevm noattr) [StructField _memory]).
        entailer!.
      }
      }
      2: {
      known_switch. forward. forward.
      { entailer!. rewrite register_values_lookup by assumption. exact I. }
      rewrite register_values_lookup by assumption. forward.
      pose proof (heap_word (frontier s) (proj1 H0)) as HeapWord.
      pose proof (c_address_order (frontier s) (regs s a) (proj1 H0) ((proj1 H1) a)) as Order.
      forward_if (store_guard_post vm ctx bytes flags owners sh code s a b v_i).
      1: {
         rewrite Order in H9. apply Nat.ltb_lt in H9.
        assert (Access : (N.to_nat (regs s a) + 8 <=? frontier s)%nat = false) by
          (apply Nat.leb_gt; lia).
        forward. unfold store_guard_post, represents_state, state_fields, represents_code, code_fields.
        Exists inactive. rewrite Access. cbn [negb Val.of_bool]. entailer!.
      }
      1: {
         rewrite Order in H9. apply Nat.ltb_ge in H9.
        forward. forward.
        unfold store_guard_post, represents_state, state_fields, represents_code, code_fields.
        Exists inactive.
        rewrite <- (c_memory_remainder (frontier s) (regs s a) (proj1 H0) H9).
        cbn [instruction_left]. entailer!.
        change (Val.of_bool (Int64.ltu (Int64.sub (Int64.repr (Z.of_nat (frontier s))) (cword (regs s a))) (Int64.repr 8)) =
          bool2val (Int64.ltu (Int64.sub (Int64.repr (Z.of_nat (frontier s))) (cword (regs s a))) (Int64.repr 8))).
        destruct (Int64.ltu (Int64.sub (Int64.repr (Z.of_nat (frontier s))) (cword (regs s a))) (Int64.repr 8)); reflexivity.
      }
      unfold store_guard_post, represents_state, state_fields. Intros inactive_after. Intros.
      forward_if.
      1: {
        assert (Access : (N.to_nat (regs s a) + 8 <=? frontier s)%nat = false).
        { destruct (N.to_nat (regs s a) + 8 <=? frontier s)%nat; auto.
          match goal with H : typed_true _ _ |- _ => unfold typed_true in H; simpl in H; discriminate end. }
        rewrite Mode. cbn [status_value state_fault]. forward_call (vm, 3, 0, 0).
        sep_apply (data_at_data_at_ Tsh (Tstruct _icevm_instruction noattr) (instruction_value (Store a b)) v_i).
        forward. unfold c_step, step. rewrite Mode, Decoded. cbn [execute]. rewrite Access.
        unfold represents_state, state_fields. Exists inactive_after.
        cbn [finish mode pc regs mem frontier frames status_value state_fault fault_number].
        try rewrite Mode. unfold represents_code, code_fields. entailer!.
      }
      1: {
        assert (Access : (N.to_nat (regs s a) + 8 <=? frontier s)%nat = true).
        { destruct (N.to_nat (regs s a) + 8 <=? frontier s)%nat; auto.
          match goal with H : typed_false _ _ |- _ => unfold typed_false in H; simpl in H; discriminate end. }
        apply Nat.leb_le in Access.
        assert (Position : (N.to_nat (regs s a) + 8 <= memory_size)%nat) by
          (eapply Nat.le_trans; [exact Access | exact (proj1 H0)]).
        assert (ZPosition : Z.of_nat (N.to_nat (regs s a)) + 8 <= 65536).
        { pose proof Position as Bound. apply Nat2Z.inj_le in Bound.
          change (Z.of_nat (N.to_nat (regs s a) + 8) <= 65536) in Bound. lia. }
        forward.
        set (loop_assert := fun progress counter : Z =>
           PROP (0 <= counter <= 8; progress <= 8)
           LOCAL (lvar _i (Tstruct _icevm_instruction noattr) v_i;
             temp _b (Vint (Int.repr counter)); temp _s vm; temp _c ctx;
             temp _address (Vlong (Int64.repr (Z.of_nat (N.to_nat (regs s a)))));
             temp _x (Vlong (cword (regs s b)));
             temp _next (Vlong (Int64.repr (Z.of_nat (pc s + width (Store a b)))));
             temp _v (Vlong Int64.zero))
           SEP (state_fields vm
               (State (pc s) (regs s)
                 (store_prefix (mem s) (N.to_nat (regs s a)) (regs s b) (Z.to_nat progress))
                 (frontier s) (frames s) Running) inactive_after;
             represents_code sh ctx bytes flags owners code;
             data_at Tsh (Tstruct _icevm_instruction noattr) (instruction_value (Store a b)) v_i)).
        forward_loop (EX n : Z, loop_assert n n)
          continue: (EX n : Z, loop_assert (n + 1) n)
          break: (dispatch_post vm ctx bytes flags owners sh code s (Store a b) v_i).
        1: {
          Exists 0. unfold loop_assert, state_fields.
          cbn [pc regs mem frontier frames mode status_value state_fault Z.to_nat].
          rewrite memory_values_store_empty. try rewrite Mode.
          unfold represents_code, code_fields. entailer!.
          unfold cword. rewrite N_nat_Z. reflexivity.
        }
        3: { forward. unfold dispatch_post. entailer!. }
        2: {
          Intros n. unfold loop_assert. Intros. forward.
          Exists (n + 1). unfold loop_assert. entailer!.
          change (Vint (Int.repr (n + 1)) = Vint (Int.add (Int.repr n) (Int.repr 1))).
          rewrite c_int_add_repr. reflexivity.
        }
        1: {
          Intros n. unfold loop_assert, state_fields. Intros.
          cbn [pc regs mem frontier frames mode status_value state_fault].
          forward_if.
          1: {
            change (n < 8) in H13.
            repeat apply -> semax_skip_seq. forward.
            1: { entailer!.
              change (Int.unsigned (Int.mul (Int.repr 8) (Int.repr n)) < 64).
              rewrite c_int_mul_repr, Int.unsigned_repr by rep_lia. lia. }
            pose proof (c_store_cast64_Z (regs s b) n ((proj1 H1) b) ltac:(lia)) as Byte.
            unfold Int64.loword, Int64.shru, cword, Int64.unsigned, Int64.repr in Byte.
            cbn [Int64.intval] in Byte.
            let eight := eval vm_compute in (Int.repr 8) in change (Int.repr 8) with eight in Byte.
            rewrite Byte.
            Exists n. unfold loop_assert, state_fields.
            cbn [pc regs mem frontier frames mode status_value state_fault].
            replace (Z.to_nat (n + 1)) with (S (Z.to_nat n)) by lia.
            rewrite memory_values_store_next by lia.
            replace (Z.of_nat (N.to_nat (regs s a) + Z.to_nat n)) with
              (Z.of_nat (N.to_nat (regs s a)) + n) by lia.
            unfold represents_code, code_fields. entailer!.
          }
          1: {
            assert (Last : n = 8) by (change (n >= 8) in H13; lia). subst n. forward.
            assert (Test : (N.to_nat (regs s a) + 8 <=? frontier s)%nat = true) by
              (apply Nat.leb_le; exact Access).
            pose proof (dispatch_canonical code s (Store a b) H1) as Canonical.
            unfold dispatch_state, execute in Canonical. rewrite Test in Canonical.
            unfold dispatch_post, represents_state, dispatch_state, execute. rewrite Test.
            Exists inactive_after. unfold state_fields.
            cbn [mode pc regs mem frontier frames status_value state_fault dispatch_value binary_instruction Z.to_nat].
            rewrite store_prefix_complete. try rewrite Mode.
            unfold represents_code, code_fields. entailer!.
          }
        }
      }
      }
      2: {
      known_switch. forward.
      pose proof (c_allocation_test (frontier s) (regs s a) (proj1 H0) ((proj1 H1) a)) as Guard.
      forward_if.
      1: {
        cbn [instruction_left] in H9.
        change (Int64.ltu (Int64.sub (Int64.repr 65536) (Int64.repr (Z.of_nat (frontier s)))) (cword (regs s a)) = true) in H9.
        rewrite Guard in H9.
        assert (Test : (frontier s + N.to_nat (regs s a) <=? memory_size)%nat = false) by
          (destruct (frontier s + N.to_nat (regs s a) <=? memory_size)%nat; auto; discriminate).
        rewrite Mode. cbn [status_value state_fault]. forward_call (vm, 3, 0, 0).
        sep_apply (data_at_data_at_ Tsh (Tstruct _icevm_instruction noattr) (instruction_value (Alloc d a)) v_i).
        forward. unfold c_step, step. rewrite Mode, Decoded. cbn [execute]. rewrite Test.
        unfold represents_state, state_fields. Exists inactive.
        cbn [finish mode pc regs mem frontier frames status_value state_fault fault_number].
        try rewrite Mode. unfold represents_code, code_fields. entailer!.
      }
      1: {
        cbn [instruction_left] in H9.
        change (Int64.ltu (Int64.sub (Int64.repr 65536) (Int64.repr (Z.of_nat (frontier s)))) (cword (regs s a)) = false) in H9.
        rewrite Guard in H9.
        assert (Test : (frontier s + N.to_nat (regs s a) <=? memory_size)%nat = true) by
          (destruct (frontier s + N.to_nat (regs s a) <=? memory_size)%nat; auto; discriminate).
        pose proof Test as Space. apply Nat.leb_le in Space.
        pose proof Space as ZSpace. apply Nat2Z.inj_le in ZSpace.
        change (Z.of_nat (frontier s + N.to_nat (regs s a)) <= 65536) in ZSpace.
        rewrite Nat2Z.inj_add in ZSpace.
        set (count := Z.of_nat (N.to_nat (regs s a))).
        assert (Count : 0 <= count <= 65536) by (unfold count; lia).
        forward. forward.
        set (loop_assert := fun progress counter : Z =>
          PROP (0 <= counter <= count; progress <= count)
          LOCAL (lvar _i (Tstruct _icevm_instruction noattr) v_i;
            temp _s vm; temp _c ctx; temp _b__1 (Vlong (Int64.repr counter));
            temp _x (Vlong (Int64.repr count));
            temp _next (Vlong (Int64.repr (Z.of_nat (pc s + width (Alloc d a)))));
            temp _v (Vlong (Int64.repr (Z.of_nat (frontier s)))))
          SEP (state_fields vm
            (State (pc s) (regs s) (clear (mem s) (frontier s) (frontier s + Z.to_nat progress))
              (frontier s) (frames s) Running) inactive;
            represents_code sh ctx bytes flags owners code;
            data_at Tsh (Tstruct _icevm_instruction noattr) (instruction_value (Alloc d a)) v_i)).
        forward_loop (EX n : Z, loop_assert n n)
          continue: (EX n : Z, loop_assert (n + 1) n)
          break: (loop_assert count count).
        1: {
          Exists 0. unfold loop_assert, state_fields.
          cbn [pc regs mem frontier frames mode status_value state_fault Z.to_nat].
          rewrite Nat.add_0_r, memory_values_clear_empty. try rewrite Mode.
          unfold represents_code, code_fields. entailer!.
          unfold count, cword. rewrite N_nat_Z. reflexivity.
        }
        2: {
          Intros n. unfold loop_assert. Intros. forward.
          Exists (n + 1). unfold loop_assert. entailer!.
        }
        2: {
          unfold loop_assert, state_fields. Intros.
          cbn [pc regs mem frontier frames mode status_value state_fault].
          forward. forward. forward. forward. forward.
          pose proof (dispatch_canonical code s (Alloc d a) H1) as Canonical.
          unfold dispatch_state, execute in Canonical. rewrite Test in Canonical.
          unfold dispatch_post, represents_state, dispatch_state, execute. rewrite Test.
          Exists inactive. unfold state_fields.
          cbn [mode pc regs mem frontier frames status_value state_fault dispatch_value binary_instruction write_reg at_pc].
          rewrite register_values_update by assumption.
          unfold count. rewrite Nat2Z.id. unfold cword. rewrite nat_N_Z.
          rewrite Nat2Z.inj_add. try rewrite Mode. unfold represents_code, code_fields.
          entailer!.
          - split; [exact Space | exact (proj2 H0)].
          - rewrite Nat2Z.inj_add. apply derives_refl.
        }
        1: {
          Intros n. unfold loop_assert, state_fields. Intros.
          cbn [pc regs mem frontier frames mode status_value state_fault].
          pose proof (c_loop_lt n count ltac:(lia) Count) as Order.
          forward_if.
          1: {
            try match goal with H : Int64.ltu _ _ = true |- _ => rewrite Order in H; apply Z.ltb_lt in H end.
            assert (Below : n < count) by rep_lia.
            repeat apply -> semax_skip_seq. forward. forward.
            Exists n. unfold loop_assert, state_fields.
            cbn [pc regs mem frontier frames mode status_value state_fault].
            replace (Z.to_nat (n + 1)) with (S (Z.to_nat n)) by lia.
            replace (frontier s + S (Z.to_nat n))%nat with (S (frontier s + Z.to_nat n))%nat by lia.
            rewrite memory_values_clear_next by (unfold count in Below; lia).
            replace (Z.of_nat (frontier s + Z.to_nat n)) with (Z.of_nat (frontier s) + n) by lia.
            unfold represents_code, code_fields. entailer!.
          }
          1: {
            assert (Last : n = count) by rep_lia. subst n. forward.
            unfold loop_assert, state_fields.
            cbn [pc regs mem frontier frames mode status_value state_fault].
            unfold represents_code, code_fields. entailer!.
          }
        }
      }
      }
      1: {
      known_switch. forward. forward_if.
      1: {
        assert (Empty : frames s = []).
        { destruct (frames s) as [|f fs] eqn:Frames; auto.
          apply (f_equal Int64.unsigned) in H9.
          change stack_size with 256%nat in H. cbn [List.length] in H.
          assert (Depth : (S (length fs) <= 256)%nat).
          { pose proof (proj2 H0) as Bound. rewrite Frames in Bound.
            cbn [List.length] in Bound. exact Bound. }
          apply Nat2Z.inj_le in Depth. change (Z.of_nat (S (length fs)) <= 256) in Depth.
          rewrite Int64.unsigned_repr in H9 by
            (cbn [List.length]; change (0 <= Z.of_nat (S (length fs)) <= 18446744073709551615); lia).
          rewrite Int64.unsigned_zero in H9. cbn [List.length] in H9. lia. }
        rewrite Mode. cbn [status_value state_fault]. forward_call (vm, 5, 0, 0).
        sep_apply (data_at_data_at_ Tsh (Tstruct _icevm_instruction noattr) (instruction_value Ret) v_i).
        forward. unfold c_step, step. rewrite Mode, Decoded. cbn [execute]. rewrite Empty.
        unfold represents_state, state_fields. Exists inactive.
        cbn [finish mode pc regs mem frontier frames status_value state_fault fault_number].
        try rewrite Mode. unfold represents_code, code_fields. entailer!.
        rewrite Empty. cbn [List.length rev map app]. apply derives_refl.
      }
      1: {
        destruct (frames s) as [|f fs] eqn:Frames; [contradiction H9; reflexivity |].
        cbn [List.length].
        change stack_size with 256%nat in H.
        assert (Depth : (S (length fs) <= 256)%nat).
          { pose proof (proj2 H0) as Bound. rewrite Frames in Bound.
            cbn [List.length] in Bound. exact Bound. }
        pose proof Depth as ZDepth. apply Nat2Z.inj_le in ZDepth.
        change (Z.of_nat (S (length fs)) <= 256) in ZDepth.
        let one := eval vm_compute in (Int.repr 1) in
          assert (Index : Z.of_nat (S (length fs)) - Int.signed one = Z.of_nat (length fs)) by
            (change (Z.of_nat (S (length fs)) - 1 = Z.of_nat (length fs)); lia).
        forward. forward.
        1: { entailer!. return_top f fs inactive. exact I. }
        return_top f fs inactive.
        pose proof (Forall_inv H3) as ReturnBound.
        forward_call (sh, ctx, flags, code, return_pc f).
        cbn [frame_value]. forward_if.
        1: {
          assert (Gate : boundary code (return_pc f) = false) by
            (destruct (boundary code (return_pc f)); auto; discriminate).
          rewrite Mode. cbn [status_value state_fault]. forward_call (vm, 2, 0, 0).
          sep_apply (data_at_data_at_ Tsh (Tstruct _icevm_instruction noattr) (instruction_value Ret) v_i).
          forward. unfold c_step, step. rewrite Mode, Decoded. cbn [execute]. rewrite Frames, Gate.
          unfold represents_state, state_fields. Exists inactive.
          cbn [finish mode pc regs mem frontier frames status_value state_fault fault_number].
          try rewrite Mode. unfold represents_code, code_fields. entailer!.
          1: { rewrite Frames. exact H. }
          rewrite Frames. cbn [List.length]. apply derives_refl.
        }
        1: {
          assert (Gate : boundary code (return_pc f) = true) by
            (destruct (boundary code (return_pc f)); auto; congruence).
          forward.
          1: { entailer!. change (0 <= 0 < 16). lia. }
          forward. forward. forward.
          Transparent reptype type_induction.type_func_rec rank_type.
          set (loop_assert := fun progress counter : Z =>
            PROP (0 <= counter <= 16; progress <= 16)
            LOCAL (lvar _i (Tstruct _icevm_instruction noattr) v_i;
              temp _r (Vint (Int.repr counter)); temp _s vm; temp _c ctx;
              temp _next (Vlong (Int64.repr (Z.of_nat (pc s + width Ret))));
              temp _v (Vlong (cword (regs s 0%nat))))
            SEP (@field_at CompSpecs Tsh (Tstruct _icevm noattr) [StructField _regs]
                   (copy_prefix (register_values (saved f)) (register_values (regs s)) progress) vm;
              @field_at CompSpecs Tsh (Tstruct _icevm noattr) [StructField _pc]
                (Vlong (Int64.repr (Z.of_nat (pc s)))) vm;
              @field_at CompSpecs Tsh (Tstruct _icevm noattr) [StructField _memory] (memory_values (mem s)) vm;
              @field_at CompSpecs Tsh (Tstruct _icevm noattr) [StructField _frontier]
                (Vlong (Int64.repr (Z.of_nat (frontier s)))) vm;
              @field_at CompSpecs Tsh (Tstruct _icevm noattr) [StructField _depth]
                (Vlong (Int64.repr (Z.of_nat (length fs)))) vm;
              @field_at CompSpecs Tsh (Tstruct _icevm noattr) [StructField _stack]
                (map frame_value (rev (f :: fs)) ++ inactive) vm;
              @field_at CompSpecs Tsh (Tstruct _icevm noattr) [StructField _status] (Vint Int.zero) vm;
              @field_at CompSpecs Tsh (Tstruct _icevm noattr) [StructField _fault] (Vint Int.zero) vm;
              represents_code sh ctx bytes flags owners code;
              data_at Tsh (Tstruct _icevm_instruction noattr) (instruction_value Ret) v_i)).
          forward_loop (EX n : Z, loop_assert n n)
            continue: (EX n : Z, loop_assert (n + 1) n)
            break: (loop_assert 16 16).
          1: {
            Exists 0. unfold loop_assert. rewrite copy_prefix_start.
            rewrite Mode. cbn [status_value state_fault]. unfold represents_code, code_fields.
            entailer!.
            change (Z.pos (Pos.of_succ_nat (length fs))) with (Z.of_nat (S (length fs))).
            rewrite Index. apply derives_refl.
          }
          2: {
            Intros n. unfold loop_assert. Intros. forward.
            Exists (n + 1). unfold loop_assert. entailer!.
            change (Vint (Int.repr (n + 1)) = Vint (Int.add (Int.repr n) (Int.repr 1))).
            rewrite c_int_add_repr. reflexivity.
          }
          1: {
            Intros n. unfold loop_assert. Intros. forward_if.
            1: {
              change (n < 16) in H13.
              repeat apply -> semax_skip_seq. forward. forward.
              1: {
                entailer!.
                change (map frame_value (rev fs ++ [f]) ++ inactive) with (map frame_value (rev (f :: fs)) ++ inactive).
                rewrite (frame_values_top f fs inactive). cbn [frame_value].
                unfold register_values. rewrite tabulated_lookup by lia. exact I.
              }
              rewrite (frame_values_top f fs inactive). cbn [frame_value]. forward.
              Exists n. unfold loop_assert.
              rewrite copy_prefix_next by (rewrite !register_values_length; lia). entailer!.
            }
            1: {
              assert (Last : n = 16) by (change (n >= 16) in H13; lia).
              subst n. forward. unfold loop_assert. entailer!.
            }
          }
          unfold loop_assert. Intros.
          assert (Copy : copy_prefix (register_values (saved f)) (register_values (regs s)) 16 = register_values (saved f)).
          { rewrite <- (register_values_length (saved f)). apply copy_prefix_complete.
            rewrite !register_values_length. reflexivity. }
          rewrite Copy. forward.
          1: { entailer!. change (0 <= 0 < 16). lia. }
          forward. forward.
          1: {
            entailer!.
            change (map frame_value (rev fs ++ [f]) ++ inactive) with (map frame_value (rev (f :: fs)) ++ inactive).
            rewrite (frame_values_top f fs inactive). cbn [frame_value]. exact I.
          }
          rewrite (frame_values_top f fs inactive). cbn [frame_value].
          forward.
          unfold dispatch_post, represents_state, dispatch_state, execute. rewrite Frames, Gate.
          Exists (frame_value f :: inactive). unfold state_fields.
          cbn [mode pc regs mem frontier frames status_value state_fault dispatch_value binary_instruction].
          pose proof (dispatch_canonical code s Ret H1) as Canonical.
          unfold represents_code, code_fields. entailer!.
          1: {
            split; [cbn [List.length]; change stack_size with 256%nat; cbn [List.length] in H; lia |].
            split; [unfold well_formed; cbn [frontier frames]; split;
              [exact (proj1 H0) | change stack_size with 256%nat; lia] |].
            split; [unfold dispatch_state, execute in Canonical; rewrite Frames, Gate in Canonical;
              exact Canonical | exact (Forall_inv_tail H3)].
          }
          rewrite (register_values_update (saved f) 0 (regs s 0%nat)) by lia.
          rewrite frame_values_pop. apply derives_refl.
        }
      }
      }
      1: {
      known_switch. forward.
      pose proof (decode_encodable _ _ _ H6 Decoded) as Encodable.
      cbn [Encoding.encodable] in Encodable. apply N.ltb_lt in Encodable.
      apply N2Z.inj_lt in Encodable. rewrite nat_N_Z in Encodable.
      change (Z.of_nat target < 18446744073709551616) in Encodable.
      assert (TargetBound : Z.of_nat target <= Int64.max_unsigned).
      { change (Z.of_nat target <= 18446744073709551615). lia. }
      assert (NextBound : Z.of_nat (pc s + width (Call target)) <= Int64.max_unsigned).
      { change (Z.of_nat (pc s + width (Call target)) <= 18446744073709551615). lia. }
      forward_call (sh, ctx, bytes, flags, owners, code, target).
      { unfold represents_code, code_fields. entailer!.
        cbn [instruction_immediate]. unfold cword. rewrite nat_N_Z. reflexivity. }
      { unfold represents_code, code_fields. entailer!. }
      set (guard_post := PROP ()
        LOCAL (lvar _i (Tstruct _icevm_instruction noattr) v_i; temp _s vm; temp _c ctx;
          temp _next (Vlong (Int64.repr (Z.of_nat (pc s + width (Call target)))));
          temp _v (Vlong Int64.zero);
          temp _t'10 (Vint (Int.repr (if (call_target code target &&
            local_target code (pc s) (pc s + width (Call target)))%bool then 0 else 1))))
        SEP (represents_state vm s; represents_code sh ctx bytes flags owners code;
          data_at Tsh (Tstruct _icevm_instruction noattr) (instruction_value (Call target)) v_i)).
      forward_if guard_post.
      1: {
        assert (Callable : call_target code target = false) by
          (destruct (call_target code target); auto; discriminate).
        forward. unfold guard_post, represents_state, state_fields. Exists inactive.
        rewrite Callable. cbn [andb]. unfold represents_code, code_fields. entailer!.
      }
      1: {
        assert (Callable : call_target code target = true) by
          (destruct (call_target code target); auto; congruence).
        forward. forward_call (sh, ctx, bytes, flags, owners, code, pc s, (pc s + width (Call target))%nat).
        forward. unfold guard_post, represents_state, state_fields. Exists inactive.
        rewrite Callable. cbn [andb]. unfold represents_code, code_fields. entailer!.
        destruct (local_target code (pc s) (pc s + width (Call target))); reflexivity.
      }
      unfold guard_post, represents_state, state_fields. Intros inactive_after. Intros. forward_if.
      1: {
        assert (Gate : (call_target code target && local_target code (pc s) (pc s + width (Call target)))%bool = false).
        { change (Int.repr (if (call_target code target && local_target code (pc s) (pc s + width (Call target)))%bool then 0 else 1) <> Int.zero) in H10.
          destruct (call_target code target && local_target code (pc s) (pc s + width (Call target)))%bool;
            [contradiction H10; reflexivity | reflexivity]. }
        rewrite Mode. cbn [status_value state_fault]. forward_call (vm, 2, 0, 0).
        sep_apply (data_at_data_at_ Tsh (Tstruct _icevm_instruction noattr) (instruction_value (Call target)) v_i).
        forward. unfold c_step, step. rewrite Mode, Decoded. cbn [execute pc at_pc]. rewrite Gate.
        unfold represents_state, state_fields. Exists inactive_after.
        cbn [finish mode pc regs mem frontier frames status_value state_fault fault_number].
        try rewrite Mode. unfold represents_code, code_fields. entailer!.
      }
      1: {
        assert (Gate : (call_target code target && local_target code (pc s) (pc s + width (Call target)))%bool = true).
        { change (Int.repr (if (call_target code target && local_target code (pc s) (pc s + width (Call target)))%bool then 0 else 1) = Int.zero) in H10.
          destruct (call_target code target && local_target code (pc s) (pc s + width (Call target)))%bool;
            [reflexivity | discriminate]. }
        forward. forward_if.
        1: {
          assert (Full : length (frames s) = stack_size).
          { apply Int64.same_if_eq in H11. apply (f_equal Int64.unsigned) in H11.
            pose proof (proj2 H0) as Depth. apply Nat2Z.inj_le in Depth.
            change (Z.of_nat (length (frames s)) <= 256) in Depth.
            change (Int64.unsigned (Int64.repr (Z.of_nat (length (frames s)))) = Int64.unsigned (Int64.repr 256)) in H11.
            rewrite !Int64.unsigned_repr in H11 by rep_lia.
            change stack_size with 256%nat. lia. }
          assert (Capacity : (length (frames s) <? stack_size)%nat = false) by (apply Nat.ltb_ge; lia).
          rewrite Mode. cbn [status_value state_fault]. forward_call (vm, 5, 0, 0).
          sep_apply (data_at_data_at_ Tsh (Tstruct _icevm_instruction noattr) (instruction_value (Call target)) v_i).
          forward. unfold c_step, step. rewrite Mode, Decoded. cbn [execute pc at_pc]. rewrite Gate, Capacity.
          unfold represents_state, state_fields. Exists inactive_after.
          cbn [finish mode pc regs mem frontier frames status_value state_fault fault_number].
          try rewrite Mode. unfold represents_code, code_fields. entailer!.
        }
        1: {
          assert (Capacity : (length (frames s) < stack_size)%nat).
          { pose proof (proj2 H0) as Depth.
            destruct (Nat.eq_dec (length (frames s)) stack_size) as [Full | Different]; [|lia].
            rewrite Full in H11. contradiction H11. reflexivity. }
          Transparent reptype type_induction.type_func_rec rank_type.
          destruct inactive_after as [|old inactive_after]; [cbn [List.length] in H9; lia |].
          destruct old as [old_pc old_regs].
          assert (Top : forall {default : Inhabitant (reptype (Tstruct _icevm_frame noattr))} old,
            Znth (Z.of_nat (length (frames s))) (map frame_value (rev (frames s)) ++ old :: inactive_after) = old).
          { intros default old. rewrite Znth_app2 by (rewrite Zlength_map, Zlength_correct, length_rev; lia).
            rewrite Zlength_map, Zlength_correct, length_rev.
            replace (Z.of_nat (length (frames s)) - Z.of_nat (length (frames s))) with 0 by lia.
            apply Znth_0_cons. }
          assert (Update : forall before after : reptype (Tstruct _icevm_frame noattr),
            upd_Znth (Z.of_nat (length (frames s))) (map frame_value (rev (frames s)) ++ before :: inactive_after) after =
            map frame_value (rev (frames s)) ++ after :: inactive_after).
          { intros before after. rewrite upd_Znth_app2 by
              (rewrite Zlength_map, Zlength_correct, length_rev, Zlength_cons;
               pose proof (Zlength_nonneg inactive_after); lia).
            rewrite Zlength_map, Zlength_correct, length_rev.
            replace (Z.of_nat (length (frames s)) - Z.of_nat (length (frames s))) with 0 by lia.
            now rewrite upd_Znth0. }
          assert (FitLength : forall p r, value_fits (Tstruct _icevm_frame noattr) (p,r) -> Zlength r = 16).
          { intros p r Fit. repeat (simplify_value_fits in Fit). tauto. }
          assert_PROP (Zlength old_regs = 16) as OldLength.
          { entailer!. simplify_value_fits in H23. destruct H23 as [_ Typed].
            apply Forall_app in Typed. apply (FitLength old_pc old_regs). exact (Forall_inv (proj2 Typed)). }
          forward. forward.
          1: { entailer!. change stack_size with 256%nat in Capacity. lia. }
          rewrite Top, Update. cbn [snd]. forward.
          set (loop_assert := fun progress counter : Z =>
            PROP (0 <= counter <= 16; progress <= 16)
            LOCAL (lvar _i (Tstruct _icevm_instruction noattr) v_i;
              temp _r__1 (Vint (Int.repr counter)); temp _s vm; temp _c ctx;
              temp _next (Vlong (Int64.repr (Z.of_nat (pc s + width (Call target)))));
              temp _v (Vlong Int64.zero))
            SEP (state_fields vm s
                ((Vlong (Int64.repr (Z.of_nat (pc s + width (Call target)))),
                  copy_prefix (register_values (regs s)) old_regs progress) :: inactive_after);
              represents_code sh ctx bytes flags owners code;
              data_at Tsh (Tstruct _icevm_instruction noattr) (instruction_value (Call target)) v_i)).
          forward_loop (EX n : Z, loop_assert n n)
            continue: (EX n : Z, loop_assert (n + 1) n)
            break: (loop_assert 16 16).
          1: {
            Exists 0. unfold loop_assert, state_fields. rewrite copy_prefix_start.
            unfold represents_code, code_fields. entailer!.
          }
          2: {
            Intros n. unfold loop_assert. Intros. forward.
            Exists (n + 1). unfold loop_assert. entailer!.
            change (Vint (Int.repr (n + 1)) = Vint (Int.add (Int.repr n) (Int.repr 1))).
            rewrite c_int_add_repr. reflexivity.
          }
          1: {
            Intros n. unfold loop_assert, state_fields. Intros. forward_if.
            1: {
              match goal with Test : n < _ |- _ => change (n < 16) in Test end.
              repeat apply -> semax_skip_seq. forward. forward.
              1: { entailer!. unfold register_values. rewrite tabulated_lookup by lia. exact I. }
              forward.
              1: { entailer!. change stack_size with 256%nat in Capacity. lia. }
              rewrite !Top, Update. cbn [fst snd]. Exists n. unfold loop_assert, state_fields.
              erewrite (copy_prefix_next (register_values (regs s)) old_regs n).
              2: { transitivity 16; [apply register_values_length | symmetry; exact OldLength]. }
              2: { rewrite register_values_length. lia. }
              entailer!.
            }
            1: {
              assert (Last : n = 16) by
                (match goal with Test : n >= _ |- _ => change (n >= 16) in Test end; lia).
              subst n. forward. unfold loop_assert, state_fields. entailer!.
            }
          }
          unfold loop_assert, state_fields. Intros.
          assert (Copy : copy_prefix (register_values (regs s)) old_regs 16 = register_values (regs s)).
          { rewrite <- (register_values_length (regs s)). apply copy_prefix_complete.
            transitivity 16; [apply register_values_length | symmetry; exact OldLength]. }
          rewrite Copy. forward. forward.
          assert (Test : (length (frames s) <? stack_size)%nat = true) by (apply Nat.ltb_lt; exact Capacity).
          forward. forward.
          unfold dispatch_post, represents_state, dispatch_state, execute. cbn [pc at_pc]. rewrite Gate, Test.
          Exists inactive_after. unfold state_fields.
          cbn [mode pc regs mem frontier frames status_value state_fault dispatch_value binary_instruction].
          pose proof (dispatch_canonical code s (Call target) H1) as Canonical.
          try rewrite Mode. unfold represents_code, code_fields. entailer!.
          1: {
            split; [cbn [instruction_value instruction_immediate]; unfold cword; rewrite nat_N_Z; reflexivity |].
            split; [cbn [List.length] in *; lia |].
            split; [unfold well_formed; cbn [frontier frames List.length]; split; [exact (proj1 H0) | lia] |].
            unfold dispatch_state, execute in Canonical. cbn [pc at_pc] in Canonical.
            rewrite Gate, Test in Canonical. exact Canonical.
          }
          rewrite frame_values_pop. cbn [frame_value return_pc saved List.length].
          let one := eval vm_compute in (Int.repr 1) in replace (Int.signed one) with 1 by reflexivity.
          replace (Z.of_nat (S (length (frames s)))) with (Z.of_nat (length (frames s)) + 1) by lia.
          apply derives_refl.
        }
      }
      }
Qed.
