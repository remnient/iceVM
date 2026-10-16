From VST.floyd Require Import proofauto.
From Stdlib Require Import NArith.
From LoosevmC Require Import CProgram.
From Loosevm Require Import Syntax State Semantics CIntegers Encoding.
Import ListNotations.
#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.
Definition register_values (r : registers) := map (fun n => Vlong (cword (r n))) (seq 0 16).
Definition memory_values (m : memory) :=
  map (fun n => Vint (Int.repr (Z.of_N (m n)))) (seq 0 memory_size).
Definition frame_value (f : frame) : reptype (Tstruct _lvm_frame noattr) :=
  (Vlong (Int64.repr (Z.of_nat (return_pc f))), register_values (saved f)).
Definition status_value (mode : status) : Z := match mode with Running => 0 | Stopped => 1 | Fault _ => 2 end.
Definition fault_number (f : fault) : Z := match f with
  | Explicit => 0 | Decode => 1 | Target => 2 | Memory => 3 | Region => 4 | Stack => 5 | Division => 6 end.
Definition state_fault (mode : status) : Z := match mode with Fault f => fault_number f | _ => 0 end.
Local Open Scope logic.
Definition state_fields p s inactive : mpred :=
  field_at Tsh (Tstruct _lvm noattr) [StructField _pc]
    (Vlong (Int64.repr (Z.of_nat (pc s)))) p *
  field_at Tsh (Tstruct _lvm noattr) [StructField _regs] (register_values (regs s)) p *
  field_at Tsh (Tstruct _lvm noattr) [StructField _memory] (memory_values (mem s)) p *
  field_at Tsh (Tstruct _lvm noattr) [StructField _frontier]
    (Vlong (Int64.repr (Z.of_nat (frontier s)))) p *
  field_at Tsh (Tstruct _lvm noattr) [StructField _depth]
    (Vlong (Int64.repr (Z.of_nat (length (frames s))))) p *
  field_at Tsh (Tstruct _lvm noattr) [StructField _stack]
    (map frame_value (rev (frames s)) ++ inactive) p *
  field_at Tsh (Tstruct _lvm noattr) [StructField _status]
    (Vint (Int.repr (status_value (mode s)))) p *
  field_at Tsh (Tstruct _lvm noattr) [StructField _fault]
    (Vint (Int.repr (state_fault (mode s)))) p.
Definition represents_state p s : mpred :=
  EX inactive : list (reptype (Tstruct _lvm_frame noattr)),
    !! ((length inactive + length (frames s) = stack_size)%nat /\ well_formed s /\ canonical s /\
        Z.of_nat (pc s) <= Int64.max_unsigned /\
        Forall (fun f => Z.of_nat (return_pc f) <= Int64.max_unsigned) (frames s)) &&
    state_fields p s inactive.
Lemma register_values_length r : Zlength (register_values r) = 16.
Proof. unfold register_values. rewrite Zlength_map, Zlength_correct, length_seq. reflexivity. Qed.
Lemma memory_values_length m : Zlength (memory_values m) = 65536.
Proof. unfold memory_values. rewrite Zlength_map, Zlength_correct, length_seq. reflexivity. Qed.

Lemma tabulated_lookup {A} {d : Inhabitant A} (f : nat -> A) size index :
  0 <= index < Z.of_nat size -> Znth index (map f (seq 0 size)) = f (Z.to_nat index).
Proof.
  intro Bounds. rewrite Znth_map by (rewrite Zlength_correct, length_seq; lia).
  unfold Znth. rewrite if_false by lia. rewrite seq_nth by lia. reflexivity.
Qed.
Lemma register_values_lookup r n : (n < 16)%nat ->
  Znth (Z.of_nat n) (register_values r) = Vlong (cword (r n)).
Proof. intro B. unfold register_values. rewrite tabulated_lookup by lia. now rewrite Nat2Z.id. Qed.
Lemma memory_values_lookup m n : (n < memory_size)%nat ->
  Znth (Z.of_nat n) (memory_values m) = Vint (Int.repr (Z.of_N (m n))).
Proof. intro B. unfold memory_values. rewrite tabulated_lookup by lia. now rewrite Nat2Z.id. Qed.
Lemma decode_position code p i : decode code p = Some i -> (p < length code)%nat.
Proof.
  destruct (Nat.lt_ge_cases p (length code)); auto.
  unfold decode. rewrite skipn_all2 by lia. discriminate.
Qed.
Lemma owner_at_bound fuel code p current target : (current <= length code)%nat ->
  (owner_at fuel code p current target <= length code)%nat.
Proof.
  revert p current. induction fuel; intros p current Bound; cbn [owner_at]; auto.
  destruct (decode code p) eqn:D; auto.
  assert (P : (p <= length code)%nat) by (apply Nat.lt_le_incl; eapply decode_position; eauto).
  destruct i; cbn; destruct (target <=? p)%nat; auto.
Qed.
Lemma owner_bound code p : (owner code p <= length code)%nat.
Proof. unfold owner. apply owner_at_bound. lia. Qed.
Definition code_values (code : list nat) := map (fun b => Vint (Int.repr (Z.of_nat b))) code.
Definition boundary_value code p := Vint (Int.repr (if boundary code p then 1 else 0)).
Definition boundary_values code := map (boundary_value code) (seq 0 (length code)).
Definition owner_value code p :=
  Vlong (Int64.repr (Z.of_nat (if boundary code p then owner code p else 0%nat))).
Definition owner_values code := map (owner_value code) (seq 0 (length code)).
Definition code_fields sh c bytes flags owners code : mpred :=
  field_at sh (Tstruct _lvm_code noattr) [StructField _bytes] bytes c *
  field_at sh (Tstruct _lvm_code noattr) [StructField _size]
    (Vlong (Int64.repr (Z.of_nat (length code)))) c *
  field_at sh (Tstruct _lvm_code noattr) [StructField _boundary] flags c *
  field_at sh (Tstruct _lvm_code noattr) [StructField _owner] owners c *
  data_at sh (tarray tuchar (Z.of_nat (length code))) (code_values code) bytes *
  data_at sh (tarray tuchar (Z.of_nat (length code))) (boundary_values code) flags *
  data_at sh (tarray tulong (Z.of_nat (length code))) (owner_values code) owners.
Definition represents_code sh c bytes flags owners code : mpred :=
  !! (readable_share sh /\ Forall (fun b => (b < 256)%nat) code /\
       Z.of_nat (length code) <= 4294967295) && code_fields sh c bytes flags owners code.
Lemma boundary_values_length code : Zlength (boundary_values code) = Z.of_nat (length code).
Proof. unfold boundary_values. rewrite Zlength_map, Zlength_correct, length_seq. reflexivity. Qed.
Lemma owner_values_length code : Zlength (owner_values code) = Z.of_nat (length code).
Proof. unfold owner_values. rewrite Zlength_map, Zlength_correct, length_seq. reflexivity. Qed.
Lemma boundary_values_lookup code p : (p < length code)%nat ->
  Znth (Z.of_nat p) (boundary_values code) = boundary_value code p.
Proof. intro B. unfold boundary_values. rewrite tabulated_lookup by lia. now rewrite Nat2Z.id. Qed.
Lemma owner_values_lookup code p : (p < length code)%nat ->
  Znth (Z.of_nat p) (owner_values code) = owner_value code p.
Proof. intro B. unfold owner_values. rewrite tabulated_lookup by lia. now rewrite Nat2Z.id. Qed.
Lemma scan_positions fuel code start :
  Forall (fun p => (p < length code)%nat) (scan fuel code start).
Proof.
  revert start. induction fuel; intro start; cbn [scan]; [constructor |].
  destruct (decode code start) eqn:D; [constructor | constructor].
  - eapply decode_position; eauto.
  - apply IHfuel.
Qed.
Lemma boundary_position code p : boundary code p = true -> (p < length code)%nat.
Proof.
  unfold boundary. intro B. apply existsb_exists in B. destruct B as [q [Present Equal]].
  apply Nat.eqb_eq in Equal. subst q.
  pose proof (scan_positions (length code) code 0) as All.
  rewrite Forall_forall in All. exact (All p Present).
Qed.
Lemma head_skipn {A} (fallback : A) xs index : hd fallback (skipn index xs) = nth index xs fallback.
Proof.
  revert index. induction xs; intros [|index]; cbn; auto.
Qed.
Local Ltac entry_tag_cases :=
  cbn [decode skipn op_decode];
  repeat first [reflexivity |
    match goal with
    | |- context [match ?xs with [] => _ | _ :: _ => _ end] => destruct xs
    | |- context [if ?b then _ else _] => destruct b
    end; cbn [op_decode]].
Lemma decode_entry_byte code p :
  (match decode code p with Some Entry => true | _ => false end) = Nat.eqb (nth p code 0%nat) 2.
Proof.
  rewrite <- (head_skipn 0%nat code p).
  unfold decode. remember (skipn p code) as bytes. destruct bytes as [|tag bytes]; [reflexivity |].
  do 28 (destruct tag as [|tag]; [entry_tag_cases |]). entry_tag_cases.
Qed.
Lemma call_target_header code p : call_target code p =
  (boundary code p && (Nat.eqb (nth p code 0%nat) 2 && negb (Nat.eqb p 0) && negb (Nat.eqb (owner code p) 0)))%bool.
Proof.
  pose proof (decode_entry_byte code p) as Header. unfold call_target.
  destruct (decode code p) as [i|]; [destruct i |]; cbn in Header;
    rewrite <- Header; destruct (boundary code p); reflexivity.
Qed.
Lemma code_values_lookup code p : (p < length code)%nat ->
  Znth (Z.of_nat p) (code_values code) = Vint (Int.repr (Z.of_nat (nth p code 0%nat))).
Proof.
  intro Bound. unfold code_values. rewrite Znth_map by (rewrite Zlength_correct; lia).
  unfold Znth. rewrite if_false by lia. now rewrite Nat2Z.id.
Qed.
Lemma code_byte_bound code p : Forall (fun b => (b < 256)%nat) code -> (p < length code)%nat ->
  (nth p code 0%nat < 256)%nat.
Proof. intros Bytes Position. rewrite Forall_forall in Bytes. apply Bytes. now apply nth_In. Qed.
Lemma byte_value_typed b : (b < 256)%nat -> is_int I8 Unsigned (Vint (Int.repr (Z.of_nat b))).
Proof.
  intro Bound. change (Int.unsigned (Int.repr (Z.of_nat b)) <= Byte.max_unsigned).
  rewrite Int.unsigned_repr by (change (0 <= Z.of_nat b <= 4294967295); lia).
  change (Z.of_nat b <= 255). lia.
Qed.

Definition instruction_opcode i : nat :=
  match i with
  | Halt => 0 | Trap => 1 | Entry => 2 | Ret => 3 | Imm _ _ => 4 | Move _ _ => 5
  | Load _ _ => 6 | Store _ _ => 7 | Alloc _ _ => 8 | Mark _ => 9 | Reset _ => 10
  | Jump _ => 11 | Branch _ _ => 12 | Indirect _ => 13 | Call _ => 14 | Nop => 15
  | Binary op _ _ _ => encode_binop op | Pad _ => 27 end.
Definition instruction_destination i :=
  match i with
  | Imm d _ | Move d _ | Binary _ d _ _ | Load d _ | Store d _ | Alloc d _ | Mark d
  | Reset d | Branch d _ | Indirect d => d | _ => 0%nat end.
Definition instruction_left i :=
  match i with Move _ a | Binary _ _ a _ | Load _ a | Store _ a | Alloc _ a => a | _ => 0%nat end.
Definition instruction_right i := match i with Binary _ _ _ b => b | _ => 0%nat end.
Definition instruction_immediate i :=
  match i with Imm _ n => n | Jump t | Branch _ t | Call t => N.of_nat t | _ => 0%N end.
Definition instruction_value i : reptype (Tstruct _lvm_instruction noattr) :=
  (Vint (Int.repr (Z.of_nat (instruction_opcode i))),
    (Vint (Int.repr (Z.of_nat (instruction_destination i))),
      (Vint (Int.repr (Z.of_nat (instruction_left i))),
        (Vint (Int.repr (Z.of_nat (instruction_right i))),
          (Vint (Int.repr (Z.of_nat (width i))), Vlong (cword (instruction_immediate i))))))).
Lemma little_capacity bytes : Forall (fun b => (b < 256)%nat) bytes ->
  (little bytes < byte_power (length bytes))%N.
Proof.
  intro B. induction B; cbn [little length byte_power]; [reflexivity |].
  assert (Byte : (N.of_nat x < 256)%N) by lia. nia.
Qed.
Local Opaque little.
Local Ltac decoded_finish E :=
  inversion E; subst; cbn [width length];
  repeat match goal with
  | H : (_ && _)%bool = true |- _ => apply andb_true_iff in H; destruct H
  | H : (_ <=? _)%nat = true |- _ => apply Nat.leb_le in H
  end; lia.
Local Ltac decoded_case E finish :=
  cbn [decode skipn op_decode] in E;
  lazymatch type of E with
  | None = Some _ => discriminate E
  | Some _ = Some _ => finish
  | context [match ?xs with [] => _ | _ :: _ => _ end] => destruct xs; decoded_case E finish
  | context [if ?b then _ else _] => destruct b eqn:?; decoded_case E finish
  end.
Lemma decoded_suffix_bounds bytes i : decode bytes 0 = Some i ->
  (1 <= width i <= 10 /\ width i <= length bytes)%nat.
Proof.
  intro E. destruct bytes as [|tag bytes]; [discriminate E |].
  do 28 (destruct tag as [|tag]; [decoded_case E ltac:(decoded_finish E) |]). decoded_case E ltac:(decoded_finish E).
Qed.
Lemma decode_bounds code p i : decode code p = Some i ->
  (1 <= width i <= 10 /\ p + width i <= length code)%nat.
Proof.
  intro D. pose proof (decode_position _ _ _ D) as Position.
  assert (Suffix : decode (skipn p code) 0 = Some i) by (unfold decode in *; cbn [skipn]; exact D).
  apply decoded_suffix_bounds in Suffix. rewrite length_skipn in Suffix. lia.
Qed.

Local Ltac decoded_register_finish E :=
  inversion E; subst; cbn [instruction_destination instruction_left instruction_right];
  repeat match goal with
  | H : (_ && _)%bool = true |- _ => apply andb_true_iff in H; destruct H
  | H : reg _ = true |- _ => unfold reg in H; apply Nat.ltb_lt in H
  end; repeat split; lia.
Lemma decoded_suffix_registers bytes i : decode bytes 0 = Some i ->
  (instruction_destination i < 16 /\ instruction_left i < 16 /\ instruction_right i < 16)%nat.
Proof.
  intro E. destruct bytes as [|tag bytes]; [discriminate E |].
  do 28 (destruct tag as [|tag]; [decoded_case E ltac:(decoded_register_finish E) |]).
  decoded_case E ltac:(decoded_register_finish E).
Qed.
Lemma decode_registers code p i : decode code p = Some i ->
  (instruction_destination i < 16 /\ instruction_left i < 16 /\ instruction_right i < 16)%nat.
Proof. unfold decode. cbn [skipn]. apply decoded_suffix_registers. Qed.
Lemma skipn_bytes count bytes : Forall (fun b => (b < 256)%nat) bytes ->
  Forall (fun b => (b < 256)%nat) (skipn count bytes).
Proof.
  revert bytes. induction count; intros bytes B; cbn [skipn]; auto.
  destruct bytes; [constructor |]. inversion B; subst. now apply IHcount.
Qed.
Local Ltac immediate_bound :=
  match goal with |- (little ?bytes < modulus)%N =>
    change (little bytes < byte_power (length bytes))%N;
    apply little_capacity; repeat (apply Forall_cons; [assumption |]); constructor
  end.
Local Ltac decoded_encodable_finish E :=
  inversion E; subst;
  repeat match goal with B : Forall _ (_ :: _) |- _ => inversion B; subst; clear B end;
  cbn [encodable];
  repeat match goal with H : (_ && _)%bool = true |- _ => apply andb_true_iff in H; destruct H end;
  repeat match goal with H : ?b = true |- context [ ?b ] => progress rewrite H end;
  first
    [ reflexivity | assumption
    | apply N.eqb_eq; apply N.mod_small; immediate_bound
    | apply N.ltb_lt; rewrite N2Nat.id; immediate_bound ].
Lemma decoded_suffix_encodable bytes i : Forall (fun b => (b < 256)%nat) bytes ->
  decode bytes 0 = Some i -> encodable i = true.
Proof.
  intros B E. destruct bytes as [|tag bytes]; [discriminate E |].
  do 28 (destruct tag as [|tag]; [decoded_case E ltac:(decoded_encodable_finish E) |]).
  decoded_case E ltac:(decoded_encodable_finish E).
Qed.
Lemma decode_encodable code p i : Forall (fun b => (b < 256)%nat) code ->
  decode code p = Some i -> encodable i = true.
Proof.
  intro B. unfold decode. cbn [skipn]. apply decoded_suffix_encodable. now apply skipn_bytes.
Qed.
