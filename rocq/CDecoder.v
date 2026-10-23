From VST.floyd Require Import proofauto.
From Stdlib Require Import NArith.
From IceVMC Require Import CProgram.
From IceVM Require Import Syntax State Semantics Encoding CIntegers CRepresentation CState CSpecification.
Import ListNotations.
Lemma skipn_head_cons {A} (d : A) xs p : (p < length xs)%nat ->
  skipn p xs = nth p xs d :: skipn (S p) xs.
Proof.
  revert xs. induction p; intros [|x xs] Bound; cbn in *; try lia; auto. apply IHp. lia.
Qed.
Lemma code_subwindow (code : list nat) a :
  sublist (Z.of_nat a) (Z.of_nat (a + 8)) code = firstn 8 (skipn a code).
Proof.
  rewrite sublist_old_sublist by lia. unfold old_sublist.
  rewrite Nat2Z.inj_add. replace (Z.of_nat a + Z.of_nat 8 - Z.of_nat a) with 8 by lia.
  now rewrite Nat2Z.id.
Qed.
Lemma eight_suffix {A} (xs : list A) : (8 <= length xs)%nat ->
  exists a b c d e f g h rest, xs = a :: b :: c :: d :: e :: f :: g :: h :: rest.
Proof.
  do 8 (destruct xs as [|? xs]; cbn [length]; [lia |]).
  intros _. repeat eexists.
Qed.
Lemma decode_jump_window code p : nth p code 0%nat = 11%nat -> (p + 9 <= length code)%nat ->
  decode code p = Some (Jump (N.to_nat (little (sublist (Z.of_nat (S p)) (Z.of_nat (S p + 8)) code)))).
Proof.
  intros Tag Enough. rewrite code_subwindow. unfold decode.
  rewrite (skipn_head_cons 0%nat code p) by lia. rewrite Tag.
  destruct (eight_suffix (skipn (S p) code)) as [a [b [c [d [e [f [g [h [rest Suffix]]]]]]]]].
  - rewrite length_skipn. lia.
  - rewrite Suffix. reflexivity.
Qed.
Lemma decode_call_window code p : nth p code 0%nat = 14%nat -> (p + 9 <= length code)%nat ->
  decode code p = Some (Call (N.to_nat (little (sublist (Z.of_nat (S p)) (Z.of_nat (S p + 8)) code)))).
Proof.
  intros Tag Enough. rewrite code_subwindow. unfold decode.
  rewrite (skipn_head_cons 0%nat code p) by lia. rewrite Tag.
  destruct (eight_suffix (skipn (S p) code)) as [a [b [c [d [e [f [g [h [rest Suffix]]]]]]]]].
  - rewrite length_skipn. lia.
  - rewrite Suffix. reflexivity.
Qed.
Lemma code_window_value code a : (a + 8 <= length code)%nat ->
  CSpecification.byte_sum (code_window code a) 8 =
    Z.of_N (little (sublist (Z.of_nat a) (Z.of_nat (a + 8)) code)).
Proof.
  intro Enough. pose proof (code_window_length code a Enough) as Length.
  assert (NaturalLength : length (code_window code a) = 8%nat) by (rewrite Zlength_correct in Length; lia).
  replace (CSpecification.byte_sum (code_window code a) 8) with
    (CSpecification.byte_sum (code_window code a) (length (code_window code a))) by now rewrite NaturalLength.
  rewrite CSpecification.byte_sum_complete. apply code_window_little.
Qed.
Lemma decode_imm_window code p : nth p code 0%nat = 4%nat -> (p + 10 <= length code)%nat ->
  decode code p = if reg (nth (S p) code 0%nat) then Some (Imm (nth (S p) code 0%nat)
    (little (sublist (Z.of_nat (S (S p))) (Z.of_nat (S (S p) + 8)) code))) else None.
Proof.
  intros Tag Enough. rewrite code_subwindow. unfold decode.
  rewrite (skipn_head_cons 0%nat code p), Tag, (skipn_head_cons 0%nat code (S p)) by lia.
  destruct (eight_suffix (skipn (S (S p)) code)) as [a [b [c [d [e [f [g [h [rest Suffix]]]]]]]]].
  - rewrite length_skipn. lia.
  - rewrite Suffix. reflexivity.
Qed.
Lemma decode_branch_window code p : nth p code 0%nat = 12%nat -> (p + 10 <= length code)%nat ->
  decode code p = if reg (nth (S p) code 0%nat) then Some (Branch (nth (S p) code 0%nat)
    (N.to_nat (little (sublist (Z.of_nat (S (S p))) (Z.of_nat (S (S p) + 8)) code)))) else None.
Proof.
  intros Tag Enough. rewrite code_subwindow. unfold decode.
  rewrite (skipn_head_cons 0%nat code p), Tag, (skipn_head_cons 0%nat code (S p)) by lia.
  destruct (eight_suffix (skipn (S (S p)) code)) as [a [b [c [d [e [f [g [h [rest Suffix]]]]]]]]].
  - rewrite length_skipn. lia.
  - rewrite Suffix. reflexivity.
Qed.
Lemma decode_binary_window code p op : nth p code 0%nat = encode_binop op -> (p + 4 <= length code)%nat ->
  decode code p = if (reg (nth (S p) code 0%nat) && reg (nth (S (S p)) code 0%nat) &&
    reg (nth (S (S (S p))) code 0%nat))%bool then
    Some (Binary op (nth (S p) code 0%nat) (nth (S (S p)) code 0%nat) (nth (S (S (S p))) code 0%nat)) else None.
Proof.
  intros Tag Enough. unfold decode.
  rewrite (skipn_head_cons 0%nat code p), Tag, (skipn_head_cons 0%nat code (S p)),
    (skipn_head_cons 0%nat code (S (S p))), (skipn_head_cons 0%nat code (S (S (S p)))) by lia.
  destruct op; reflexivity.
Qed.
Lemma arithmetic_opcode n : (16 <= n <= 26)%nat -> exists op, n = encode_binop op.
Proof.
  intro Range. do 27 (destruct n as [|n]; [cbn [encode_binop] in *;
    first [lia | exists Add; reflexivity | exists Sub; reflexivity | exists Mul; reflexivity |
      exists Div; reflexivity | exists And; reflexivity | exists Or; reflexivity | exists Xor; reflexivity |
      exists Shl; reflexivity | exists Shr; reflexivity | exists Eq; reflexivity | exists Lt; reflexivity] |]). lia.
Qed.

Definition encoded_width (tag : nat) : nat :=
  (match tag with
  | 0 | 1 | 2 | 3 | 15 => 1
  | 4 | 12 => 10
  | 5 | 6 | 7 | 8 => 3
  | 9 | 10 | 13 => 2
  | 11 | 14 => 9
  | _ => 4 end)%nat.
Local Ltac suffix_cases E finish :=
  cbn [decode skipn op_decode] in E;
  lazymatch type of E with
  | None = Some _ => discriminate E
  | Some _ = Some _ => inversion E; subst; finish
  | context [match ?xs with [] => _ | _ :: _ => _ end] => destruct xs; suffix_cases E finish
  | context [if ?b then _ else _] => destruct b; suffix_cases E finish
  end.
Lemma suffix_fixed_width bytes ins : hd 0%nat bytes <> 27%nat ->
  decode bytes 0 = Some ins -> width ins = encoded_width (hd 0%nat bytes).
Proof.
  intros Tag D. destruct bytes as [|tag bytes]; [discriminate D |].
  cbn [hd] in *.
  do 28 (destruct tag as [|tag];
    [suffix_cases D ltac:(cbn [width encoded_width] in *; congruence) |]).
  suffix_cases D ltac:(cbn [width encoded_width] in *; congruence).
Qed.
Lemma decode_fixed_width code p ins : nth p code 0%nat <> 27%nat ->
  decode code p = Some ins -> width ins = encoded_width (nth p code 0%nat).
Proof.
  intros Tag D. rewrite <- head_skipn in *.
  apply suffix_fixed_width; [assumption |]. unfold decode in *. exact D.
Qed.
Lemma decode_insufficient code p : nth p code 0%nat <> 27%nat ->
  (length code - p < encoded_width (nth p code 0%nat))%nat -> decode code p = None.
Proof.
  intros Tag Short. destruct (decode code p) as [ins|] eqn:D; auto.
  pose proof (decode_bounds _ _ _ D) as Bounds.
  pose proof (decode_fixed_width _ _ _ Tag D) as Width. lia.
Qed.
Lemma suffix_instruction_opcode bytes ins : decode bytes 0 = Some ins ->
  instruction_opcode ins = hd 0%nat bytes.
Proof.
  intro D. destruct bytes as [|tag bytes]; [discriminate D |].
  do 28 (destruct tag as [|tag];
    [suffix_cases D ltac:(reflexivity) |]).
  suffix_cases D ltac:(reflexivity).
Qed.
Lemma decode_instruction_opcode code p ins : decode code p = Some ins ->
  instruction_opcode ins = nth p code 0%nat.
Proof.
  intro D. rewrite <- head_skipn. apply suffix_instruction_opcode.
  unfold decode in *. exact D.
Qed.
Lemma instruction_opcode_bound ins : (instruction_opcode ins <= 27)%nat.
Proof.
  destruct ins; cbn [instruction_opcode]; try lia. destruct op; cbn [encode_binop]; lia.
Qed.
Lemma decode_invalid_tag code p : (27 < nth p code 0%nat)%nat -> decode code p = None.
Proof.
  intro Tag. destruct (decode code p) as [ins|] eqn:D; [|reflexivity].
  pose proof (decode_instruction_opcode _ _ _ D). pose proof (instruction_opcode_bound ins). lia.
Qed.
Lemma byte_address b i n p k :
  0 <= p <= Int64.max_unsigned -> 0 <= k <= Int.max_signed ->
  0 <= p + k < n -> field_compatible (tarray tuchar n) [] (Vptr b i) ->
  Vptr b (Ptrofs.add
    (Ptrofs.add i (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_int64 (Int64.repr p))))
    (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_ints (Int.repr k)))) =
  field_address (tarray tuchar n) [ArraySubsc (p + k)] (Vptr b i).
Proof.
  intros Position Offset Index Compatible.
  rewrite field_address_offset by auto with field_compatible.
  unfold Ptrofs.of_int64, Ptrofs.of_ints.
  rewrite Int64.unsigned_repr by lia. rewrite Int.signed_repr by rep_lia.
  cbn [nested_field_offset nested_field_rec tarray tuchar sizeof offset_val].
  autorewrite with norm. reflexivity.
Qed.
Lemma remaining_unsigned n p : 0 <= p <= n -> n <= Int64.max_unsigned ->
  Int64.unsigned (Int64.sub (Int64.repr n) (Int64.repr p)) = n - p.
Proof.
  intros Range Bound. unfold Int64.sub.
  rewrite (Int64.unsigned_repr n) by lia. rewrite (Int64.unsigned_repr p) by lia.
  apply Int64.unsigned_repr. lia.
Qed.
Lemma decode_padding code p : nth p code 0%nat = 27%nat ->
  decode code p =
  if (p + 2 <=? length code)%nat then
    if ((nth (S p) code 0%nat <=? 8)%nat &&
        (p + 2 + nth (S p) code 0%nat <=? length code)%nat)%bool
    then Some (Pad (nth (S p) code 0%nat)) else None
  else None.
Proof.
  intro Tag.
  assert (Position : (p < length code)%nat).
  { destruct (Nat.lt_ge_cases p (length code)); [assumption |].
    rewrite nth_overflow in Tag by lia. discriminate. }
  destruct (p + 2 <=? length code)%nat eqn:Size.
  - apply Nat.leb_le in Size. unfold decode.
    rewrite (skipn_head_cons 0%nat code p), Tag,
      (skipn_head_cons 0%nat code (S p)) by lia.
    rewrite length_skipn.
    destruct (nth (S p) code 0%nat <=? 8)%nat; cbn [andb]; [|reflexivity].
    destruct (nth (S p) code 0%nat <=? length code - S (S p))%nat eqn:Available;
      destruct (p + 2 + nth (S p) code 0%nat <=? length code)%nat eqn:Fit; try reflexivity;
      apply Nat.leb_le in Available || apply Nat.leb_gt in Available;
      apply Nat.leb_le in Fit || apply Nat.leb_gt in Fit; lia.
  - apply Nat.leb_gt in Size. unfold decode.
    rewrite (skipn_head_cons 0%nat code p), Tag by lia.
    rewrite skipn_all2 by lia. reflexivity.
Qed.
Local Ltac decoder_cases :=
  repeat match goal with
  | Negative : Int.unsigned (Int.repr _) <> Int.unsigned (Int.repr _) |- _ => clear Negative
  | Equal : Z.of_nat (nth _ _ 0%nat) = _ |- _ => clear Equal
  end.
Local Ltac decoder_forget output :=
  match goal with |- context [data_at Tsh (Tstruct _icevm_instruction noattr) ?value output] =>
    sep_apply (data_at_data_at_ Tsh (Tstruct _icevm_instruction noattr) value output)
  end.
Local Ltac decoder_byte b i code p offset index :=
  let Array := fresh "Array" in let Address := fresh "Address" in
  assert_PROP (field_compatible (tarray tuchar (Z.of_nat (length code))) [] (Vptr b i)) as Array by entailer!;
  pose proof (byte_address b i (Z.of_nat (length code)) (Z.of_nat p) offset
    ltac:(rep_lia) ltac:(rep_lia) ltac:(lia) Array) as Address;
  replace (Z.of_nat p + offset) with (Z.of_nat index) in Address by lia;
  forward;
  [entailer!; change (is_int I8 Unsigned (Znth (Z.of_nat index) (code_values code)));
    rewrite code_values_lookup by lia;
    apply byte_value_typed; eapply code_byte_bound; eauto; lia
  | fold (Z.of_nat index); rewrite code_values_lookup by lia].
Local Ltac decoder_comparison :=
  unfold Int.ltu; rewrite !Int.unsigned_repr by rep_lia;
  first [rewrite if_true by lia | rewrite if_false by lia]; reflexivity.
Local Ltac decoder_remaining remaining width :=
  match goal with
  | Condition : (Int64.unsigned (Int64.sub _ _) < _)%Z |- _ =>
    rewrite remaining in Condition; change (Int64.unsigned (Int64.repr width)) with width in Condition
  | Condition : (Int64.unsigned (Int64.sub _ _) >= _)%Z |- _ =>
    rewrite remaining in Condition; change (Int64.unsigned (Int64.repr width)) with width in Condition
  end.
Local Ltac decoder_register constructor tag b i output code p :=
  let Tag := fresh "Tag" in let Remaining := fresh "Remaining" in
  let Missing := fresh "Missing" in let Enough := fresh "Enough" in
  let Decoded := fresh "Decoded" in let Operand := fresh "Operand" in let Register := fresh "Register" in
  assert (Tag : nth p code 0%nat = tag) by lia; decoder_cases;
  pose proof (remaining_unsigned (Z.of_nat (length code)) (Z.of_nat p)
    ltac:(lia) ltac:(rep_lia)) as Remaining;
  forward; forward_if;
  [decoder_remaining Remaining 2;
    assert (Missing : decode code p = None) by
      (apply decode_insufficient; rewrite Tag; [discriminate | cbn [encoded_width]; lia]);
    forward; unfold decode_result; rewrite Missing; decoder_forget output; entailer!
  |decoder_remaining Remaining 2;
    assert (Enough : (p + 2 <= length code)%nat) by lia;
    forward; decoder_byte b i code p 1 (S p); forward; forward;
    assert (Decoded : decode code p =
      if reg (nth (S p) code 0%nat) then Some (constructor (nth (S p) code 0%nat)) else None) by
      (unfold decode; match goal with Suffix : skipn _ _ = _ |- _ => rewrite Suffix end; rewrite Tag, (skipn_head_cons 0%nat code (S p)) by lia; reflexivity);
    assert (Operand : (nth (S p) code 0%nat < 256)%nat) by (eapply code_byte_bound; eauto; lia);
    destruct (reg (nth (S p) code 0%nat)) eqn:Register;
    [unfold reg in Register; apply Nat.ltb_lt in Register;
      forward; unfold decode_result; rewrite Decoded;
      unfold instruction_value, instruction_opcode, instruction_destination, instruction_left,
        instruction_right, instruction_immediate, width, cword; rewrite Tag; entailer!;
      decoder_comparison
    |unfold reg in Register; apply Nat.ltb_ge in Register;
      forward; unfold decode_result; rewrite Decoded; decoder_forget output; entailer!;
      decoder_comparison]].
Lemma register_comparison n :
  bool2val (Coqlib.zlt (Z.of_nat n) 16) = Vint (Int.repr (if reg n then 1 else 0)).
Proof.
  unfold reg. destruct (Coqlib.zlt (Z.of_nat n) 16); destruct (n <? 16)%nat eqn:R;
    try reflexivity; apply Nat.ltb_lt in R || apply Nat.ltb_ge in R; exfalso; lia.
Qed.
Local Ltac decoder_two constructor tag b i output code p :=
  let Tag := fresh "Tag" in let Remaining := fresh "Remaining" in
  let Missing := fresh "Missing" in let Enough := fresh "Enough" in
  let Decoded := fresh "Decoded" in let Both := fresh "Both" in
  let Destination := fresh "Destination" in let Source := fresh "Source" in let Register := fresh "Register" in
  assert (Tag : nth p code 0%nat = tag) by lia; decoder_cases;
  pose proof (remaining_unsigned (Z.of_nat (length code)) (Z.of_nat p)
    ltac:(lia) ltac:(rep_lia)) as Remaining;
  forward; forward_if;
  [decoder_remaining Remaining 3;
    assert (Missing : decode code p = None) by
      (apply decode_insufficient; rewrite Tag; [discriminate | cbn [encoded_width]; lia]);
    forward; unfold decode_result; rewrite Missing; decoder_forget output; entailer!
  |decoder_remaining Remaining 3;
    assert (Enough : (p + 3 <= length code)%nat) by lia;
    forward; decoder_byte b i code p 1 (S p); forward;
    decoder_byte b i code p 2 (S (S p)); forward; forward;
    assert (Destination : (nth (S p) code 0%nat < 256)%nat) by (eapply code_byte_bound; eauto; lia);
    assert (Source : (nth (S (S p)) code 0%nat < 256)%nat) by (eapply code_byte_bound; eauto; lia);
    assert (Decoded : decode code p =
      if (reg (nth (S p) code 0%nat) && reg (nth (S (S p)) code 0%nat))%bool
      then Some (constructor (nth (S p) code 0%nat) (nth (S (S p)) code 0%nat)) else None) by
      (unfold decode; match goal with Suffix : skipn _ _ = _ |- _ => rewrite Suffix end;
        rewrite Tag, (skipn_head_cons 0%nat code (S p)), (skipn_head_cons 0%nat code (S (S p))) by lia;
        reflexivity);
    forward_if (temp _t'5 (Vint (Int.repr
      (if (reg (nth (S p) code 0%nat) && reg (nth (S (S p)) code 0%nat))%bool then 1 else 0))));
    [assert (Register : reg (nth (S p) code 0%nat) = true) by (unfold reg; apply Nat.ltb_lt; rep_lia);
      forward; forward; entailer!; rewrite Register; cbn [andb];
      rewrite register_comparison; reflexivity
    |assert (Register : reg (nth (S p) code 0%nat) = false) by (unfold reg; apply Nat.ltb_ge; rep_lia);
      forward; entailer!; rewrite Register; reflexivity
    |destruct ((reg (nth (S p) code 0%nat) && reg (nth (S (S p)) code 0%nat))%bool) eqn:Both;
      forward; unfold decode_result; rewrite Decoded;
      [unfold instruction_value, instruction_opcode, instruction_destination, instruction_left,
        instruction_right, instruction_immediate, width, cword; rewrite Tag; entailer!
      |decoder_forget output; entailer!]]].

Local Ltac decoder_read64 sh b i code p offset index :=
  let Array := fresh "Array" in
  assert_PROP (field_compatible (tarray tuchar (Z.of_nat (length code))) [] (Vptr b i)) as Array by entailer!;
  rewrite (byte_window_split sh (Z.of_nat (length code)) (code_values code) (Vptr b i) (Z.of_nat index))
    by (unfold code_values; rewrite ?Zlength_map, ?Zlength_correct; lia);
  replace (Z.of_nat index + 8) with (Z.of_nat (index + 8)) by lia;
  rewrite code_values_window;
  forward_call (field_address0 (tarray tuchar (Z.of_nat (length code))) [ArraySubsc (Z.of_nat index)] (Vptr b i),
    sh, code_window code index);
  [entailer!; rewrite field_address0_offset by auto with field_compatible;
    cbn [nested_field_offset nested_field_rec tarray tuchar sizeof offset_val];
    change ([Vptr b (Ptrofs.add (Ptrofs.add i
      (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_int64 (Int64.repr (Z.of_nat p)))))
      (Ptrofs.repr offset))] = [Vptr b (Ptrofs.add i (Ptrofs.repr (Z.of_nat index)))]);
    unfold Ptrofs.of_int64; rewrite Int64.unsigned_repr by rep_lia;
    replace (Z.of_nat index) with (Z.of_nat p + offset) by lia;
    autorewrite with norm; reflexivity
  |cancel
  |split; [apply code_window_length; lia | now apply code_window_bytes]
  |rewrite <- code_values_window;
    replace (Z.of_nat (index + 8)) with (Z.of_nat index + 8) by lia;
    sep_apply (byte_window_join sh (Z.of_nat (length code)) (code_values code) (Vptr b i) (Z.of_nat index)
      ltac:(lia) ltac:(lia) ltac:(unfold code_values; rewrite Zlength_map, Zlength_correct; reflexivity));
    rewrite code_window_value by lia].
Local Ltac decoder_target tag view sh b i output code p :=
  let Tag := fresh "Tag" in let Remaining := fresh "Remaining" in
  let Missing := fresh "Missing" in let Enough := fresh "Enough" in
  assert (Tag : nth p code 0%nat = tag) by lia; decoder_cases;
  pose proof (remaining_unsigned (Z.of_nat (length code)) (Z.of_nat p)
    ltac:(lia) ltac:(rep_lia)) as Remaining;
  forward; forward_if;
  [decoder_remaining Remaining 9;
    assert (Missing : decode code p = None) by
      (apply decode_insufficient; rewrite Tag; [discriminate | cbn [encoded_width]; lia]);
    forward; unfold decode_result; rewrite Missing; decoder_forget output; entailer!
  |decoder_remaining Remaining 9;
    assert (Enough : (p + 9 <= length code)%nat) by lia;
    forward; decoder_read64 sh b i code p 1 (S p); forward; forward;
    unfold decode_result; rewrite (view code p Tag Enough);
    unfold instruction_value, instruction_opcode, instruction_destination, instruction_left,
      instruction_right, instruction_immediate, width, cword;
    rewrite N2Nat.id, Tag; entailer!].
Local Ltac decoder_immediate tag view sh b i output code p :=
  let Tag := fresh "Tag" in let Remaining := fresh "Remaining" in
  let Missing := fresh "Missing" in let Enough := fresh "Enough" in
  let Decoded := fresh "Decoded" in let Operand := fresh "Operand" in let Register := fresh "Register" in
  assert (Tag : nth p code 0%nat = tag) by lia; decoder_cases;
  pose proof (remaining_unsigned (Z.of_nat (length code)) (Z.of_nat p)
    ltac:(lia) ltac:(rep_lia)) as Remaining;
  forward; forward_if;
  [decoder_remaining Remaining 10;
    assert (Missing : decode code p = None) by
      (apply decode_insufficient; rewrite Tag; [discriminate | cbn [encoded_width]; lia]);
    forward; unfold decode_result; rewrite Missing; decoder_forget output; entailer!
  |decoder_remaining Remaining 10;
    assert (Enough : (p + 10 <= length code)%nat) by lia;
    forward; decoder_byte b i code p 1 (S p); forward;
    decoder_read64 sh b i code p 2 (S (S p)); forward; forward;
    pose proof (view code p Tag Enough) as Decoded;
    assert (Operand : (nth (S p) code 0%nat < 256)%nat) by (eapply code_byte_bound; eauto; lia);
    destruct (reg (nth (S p) code 0%nat)) eqn:Register;
    [unfold reg in Register; apply Nat.ltb_lt in Register;
      forward; unfold decode_result; rewrite Decoded;
      unfold instruction_value, instruction_opcode, instruction_destination, instruction_left,
        instruction_right, instruction_immediate, width, cword;
      rewrite ?N2Nat.id, Tag; entailer!; decoder_comparison
    |unfold reg in Register; apply Nat.ltb_ge in Register;
      forward; unfold decode_result; rewrite Decoded; decoder_forget output; entailer!; decoder_comparison]].

Lemma arithmetic_comparison n :
  bool2val (Coqlib.zlt 26 (Z.of_nat n)) = Vint (Int.repr (if (26 <? n)%nat then 1 else 0)).
Proof.
  destruct (Coqlib.zlt 26 (Z.of_nat n)); destruct (26 <? n)%nat eqn:R; try reflexivity;
    apply Nat.ltb_lt in R || apply Nat.ltb_ge in R; exfalso; lia.
Qed.
Lemma flag_zero (b : bool) : Int.repr (if b then 1 else 0) = Int.zero -> b = false.
Proof.
  destruct b; [|reflexivity]. intro Equal. apply (f_equal Int.unsigned) in Equal.
  rewrite Int.unsigned_repr, Int.unsigned_zero in Equal by rep_lia. discriminate.
Qed.
Lemma flag_nonzero (b : bool) : Int.repr (if b then 1 else 0) <> Int.zero -> b = true.
Proof. destruct b; [reflexivity | contradiction]. Qed.
Lemma encoded_width_opcode op : encoded_width (encode_binop op) = 4%nat.
Proof. destruct op; reflexivity. Qed.
Lemma decode_arithmetic_guard code p : (16 <= nth p code 0%nat)%nat -> nth p code 0%nat <> 27%nat ->
  ((26 <? nth p code 0%nat)%nat || (length code - p <? 4)%nat)%bool = true -> decode code p = None.
Proof.
  intros Lower NotPad Guard. destruct (26 <? nth p code 0%nat)%nat eqn:High.
  - apply Nat.ltb_lt in High. apply decode_invalid_tag. lia.
  - cbn [orb] in Guard. apply Nat.ltb_ge in High. apply Nat.ltb_lt in Guard.
    destruct (arithmetic_opcode (nth p code 0%nat) ltac:(lia)) as [op Tag].
    apply decode_insufficient; [exact NotPad |]. rewrite Tag, encoded_width_opcode. exact Guard.
Qed.

Lemma body_decoder : semax_body Vprog Gprog f_icevm_decode decoder_spec.
Proof.
  start_function. forward. forward_if.
  - assert (Outside : (length code <= p)%nat) by rep_lia.
    assert (Missing : decode code p = None) by (unfold decode; rewrite skipn_all2 by assumption; reflexivity).
    forward. unfold decode_result. rewrite Missing. entailer!.
  - assert (Inside : (p < length code)%nat) by rep_lia.
    assert_PROP (isptr bytes) as Pointer by entailer!.
    destruct bytes; try contradiction.
    forward. forward.
    assert_PROP (Vptr b (Ptrofs.add
      (Ptrofs.add i (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_int64 (Int64.repr (Z.of_nat p)))))
      (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_ints (Int.repr 0)))) =
      field_address (tarray tuchar (Z.of_nat (length code))) [ArraySubsc (Z.of_nat p)] (Vptr b i)) as HeaderAddress.
    { entailer!. rewrite field_address_offset by auto with field_compatible.
      unfold Ptrofs.of_int64, Ptrofs.of_ints.
      rewrite Int64.unsigned_repr by lia. cbn [nested_field_offset nested_field_rec tarray tuchar sizeof offset_val]. autorewrite with norm. reflexivity. }
    assert (Byte : (nth p code 0%nat < 256)%nat) by (eapply code_byte_bound; eauto).
    forward.
    { entailer!. rewrite code_values_lookup by assumption. now apply byte_value_typed. }
    rewrite code_values_lookup by assumption.
    do 10 forward.
    assert (Suffix : skipn p code = nth p code 0%nat :: skipn (S p) code)
      by (apply skipn_head_cons; assumption).
    forward_if.
    all: try solve [
      match goal with E : Z.of_nat (nth ?pos ?contents 0%nat) = ?k,
        Suffix : skipn _ _ = _ |- _ =>
        let ins := lazymatch k with 0 => constr:(Halt) | 1 => constr:(Trap)
          | 2 => constr:(Entry) | 3 => constr:(Ret) | 15 => constr:(Nop) end in
        let tag := eval compute in (Z.to_nat k) in
        assert (Tag : nth pos contents 0%nat = tag) by lia;
        assert (Decoded : decode contents pos = Some ins) by
          (unfold decode; rewrite Suffix, Tag; reflexivity);
        forward; forward; unfold decode_result; rewrite Decoded; entailer!;
        rewrite Tag; unfold instruction_value, instruction_opcode, instruction_destination,
          instruction_left, instruction_right, instruction_immediate, width, cword;
        apply derives_refl
      end].
    7: decoder_register Mark 9%nat b i output code p.
    7: decoder_register Reset 10%nat b i output code p.
    7: decoder_register Indirect 13%nat b i output code p.
    3: decoder_two Move 5%nat b i output code p.
    3: decoder_two Load 6%nat b i output code p.
    3: decoder_two Store 7%nat b i output code p.
    3: decoder_two Alloc 8%nat b i output code p.
    5: {
      assert (Tag : nth p code 0%nat = 27%nat) by lia. decoder_cases.
      pose proof (remaining_unsigned (Z.of_nat (length code)) (Z.of_nat p)
        ltac:(lia) ltac:(rep_lia)) as Remaining.
      set (Gate := ((p + 2 <=? length code)%nat && (nth (S p) code 0%nat <=? 8)%nat)%bool).
      forward.
      forward_if (temp _t'7 (Vint (Int.repr (if Gate then 0 else 1)))).
      - decoder_remaining Remaining 2.
        assert (Size : (p + 2 <=? length code)%nat = false) by (apply Nat.leb_gt; lia).
        forward. entailer!. unfold Gate. now rewrite Size.
      - decoder_remaining Remaining 2.
        assert (Enough : (p + 2 <= length code)%nat) by lia.
        assert (Size : (p + 2 <=? length code)%nat = true) by (apply Nat.leb_le; lia).
        assert (Operand : (nth (S p) code 0%nat < 256)%nat) by (eapply code_byte_bound; eauto; lia).
        decoder_byte b i code p 1 (S p). forward. entailer!.
        unfold Gate. rewrite Size. cbn [andb].
        destruct (nth (S p) code 0%nat <=? 8)%nat eqn:Count;
          destruct (Coqlib.zlt 8 (Z.of_nat (nth (S p) code 0%nat))); try reflexivity;
          apply Nat.leb_le in Count || apply Nat.leb_gt in Count; exfalso; lia.
      - forward_if.
        + assert (Bad : Gate = false) by (destruct Gate; [congruence | reflexivity]).
          assert (Missing : decode code p = None).
          { rewrite (decode_padding code p Tag). unfold Gate in Bad.
            destruct (p + 2 <=? length code)%nat; [|reflexivity].
            cbn [andb] in Bad. now rewrite Bad. }
          forward. unfold decode_result. rewrite Missing. decoder_forget output. entailer!.
        + assert (Good : Gate = true).
          { destruct Gate eqn:G; [reflexivity |].
            apply (f_equal Int.unsigned) in H3.
            rewrite Int.unsigned_repr, Int.unsigned_zero in H3 by rep_lia. lia. }
          unfold Gate in Good. apply andb_true_iff in Good. destruct Good as [Size Count].
          pose proof Size as Enough. apply Nat.leb_le in Enough.
          pose proof Count as Limit. apply Nat.leb_le in Limit.
          decoder_byte b i code p 1 (S p). forward.
          rewrite c_int_add_repr.
          replace (2 + Z.of_nat (nth (S p) code 0%nat)) with
            (Z.of_nat (2 + nth (S p) code 0%nat)) by lia.
          forward. forward.
          assert (Decoded : decode code p =
            if (p + 2 + nth (S p) code 0%nat <=? length code)%nat
            then Some (Pad (nth (S p) code 0%nat)) else None).
          { rewrite (decode_padding code p Tag), Size, Count. reflexivity. }
          destruct (p + 2 + nth (S p) code 0%nat <=? length code)%nat eqn:Fit.
          * apply Nat.leb_le in Fit. forward. unfold decode_result. rewrite Decoded.
            unfold instruction_value, instruction_opcode, instruction_destination, instruction_left,
              instruction_right, instruction_immediate, width, cword. rewrite Tag. entailer!.
            unfold Int64.ltu. rewrite !Int64.unsigned_repr by rep_lia.
            rewrite if_false by lia. reflexivity.
          * apply Nat.leb_gt in Fit. forward. unfold decode_result. rewrite Decoded.
            decoder_forget output. entailer!.
            unfold Int64.ltu. rewrite !Int64.unsigned_repr by rep_lia.
            rewrite if_true by lia. reflexivity.
    }
    3: decoder_target 11%nat decode_jump_window sh b i output code p.
    3: decoder_target 14%nat decode_call_window sh b i output code p.
    1: decoder_immediate 4%nat decode_imm_window sh b i output code p.
    1: decoder_immediate 12%nat decode_branch_window sh b i output code p.
    {

      repeat match goal with Negative : Int.unsigned (Int.repr _) <> Int.unsigned (Int.repr _) |- _ =>
        rewrite !Int.unsigned_repr in Negative by rep_lia end.
      assert (Lower : (16 <= nth p code 0%nat)%nat) by rep_lia.
      assert (NotPad : nth p code 0%nat <> 27%nat) by lia.
      repeat match goal with Negative : Z.of_nat (nth _ _ 0%nat) <> _ |- _ => clear Negative end.
      set (High := (26 <? nth p code 0%nat)%nat).
      set (Short := (length code - p <? 4)%nat).
      set (Gate := (High || Short)%bool).
      forward.
      forward_if (temp _t'8 (Vint (Int.repr (if High then 1 else 0)))).
      - exfalso. rep_lia.
      - forward. forward. entailer!. symmetry. apply arithmetic_comparison.
      - pose proof (remaining_unsigned (Z.of_nat (length code)) (Z.of_nat p)
          ltac:(lia) ltac:(rep_lia)) as Remaining.
        forward_if (temp _t'9 (Vint (Int.repr (if Gate then 1 else 0)))).
        + assert (HighTrue : High = true) by (destruct High; auto; contradiction).
          forward. entailer!. unfold Gate. now rewrite HighTrue.
        + assert (HighFalse : High = false).
          { destruct High; auto. exfalso.
            match goal with Bad : Int.repr 1 = Int.zero |- _ =>
              apply (f_equal Int.unsigned) in Bad;
              rewrite Int.unsigned_repr, Int.unsigned_zero in Bad by rep_lia; lia end. }
          forward. forward. entailer!. unfold Gate. rewrite HighFalse. cbn [orb].
          try rewrite Remaining. rewrite ?Int64.unsigned_repr by rep_lia. unfold Short.
          destruct (length code - p <? 4)%nat eqn:Size;
            apply Nat.ltb_lt in Size || apply Nat.ltb_ge in Size;
            cbn [Int64.cmpu]; unfold Int64.ltu; rewrite ?Int64.unsigned_repr by rep_lia;
            unfold bool2val; first [rewrite if_true by lia | rewrite if_false by lia]; reflexivity.
        + forward_if.
          * assert (Bad : Gate = true) by (apply flag_nonzero; assumption).
            assert (Missing : decode code p = None).
            { apply decode_arithmetic_guard; [exact Lower | exact NotPad | exact Bad]. }
            forward. unfold decode_result. rewrite Missing. decoder_forget output. entailer!.
          * assert (Good : Gate = false) by (apply flag_zero; assumption).
            unfold Gate, High, Short in Good. apply orb_false_iff in Good.
            destruct Good as [Upper Enough]. apply Nat.ltb_ge in Upper, Enough.
            assert (Space : (p + 4 <= length code)%nat) by lia.
            destruct (arithmetic_opcode (nth p code 0%nat) ltac:(lia)) as [op Tag].
            forward. decoder_byte b i code p 1 (S p). forward.
            decoder_byte b i code p 2 (S (S p)). forward.
            decoder_byte b i code p 3 (S (S (S p))). forward. forward.
            assert (Destination : (nth (S p) code 0%nat < 256)%nat) by (eapply code_byte_bound; eauto; lia).
            assert (Left : (nth (S (S p)) code 0%nat < 256)%nat) by (eapply code_byte_bound; eauto; lia).
            assert (Right : (nth (S (S (S p))) code 0%nat < 256)%nat) by (eapply code_byte_bound; eauto; lia).
            forward_if (temp _t'10 (Vint (Int.repr
              (if (reg (nth (S p) code 0%nat) && reg (nth (S (S p)) code 0%nat))%bool then 1 else 0)))).
            -- assert (Register : reg (nth (S p) code 0%nat) = true) by (unfold reg; apply Nat.ltb_lt; rep_lia).
               forward. forward. entailer!. rewrite Register. cbn [andb]. rewrite register_comparison. reflexivity.
            -- assert (Register : reg (nth (S p) code 0%nat) = false) by (unfold reg; apply Nat.ltb_ge; rep_lia).
               forward. entailer!. rewrite Register. reflexivity.
            -- forward_if (temp _t'11 (Vint (Int.repr
                 (if (reg (nth (S p) code 0%nat) && reg (nth (S (S p)) code 0%nat) &&
                   reg (nth (S (S (S p))) code 0%nat))%bool then 1 else 0)))).
               ++ assert (Pair : (reg (nth (S p) code 0%nat) && reg (nth (S (S p)) code 0%nat))%bool = true)
                    by (apply flag_nonzero; assumption).
                  forward. forward. entailer!. rewrite Pair. cbn [andb]. rewrite register_comparison. reflexivity.
               ++ assert (Pair : (reg (nth (S p) code 0%nat) && reg (nth (S (S p)) code 0%nat))%bool = false)
                    by (apply flag_zero; assumption).
                  forward. entailer!. rewrite Pair. reflexivity.
               ++ pose proof (decode_binary_window code p op Tag Space) as Decoded.
                  destruct ((reg (nth (S p) code 0%nat) && reg (nth (S (S p)) code 0%nat) &&
                    reg (nth (S (S (S p))) code 0%nat))%bool) eqn:Both;
                    forward; unfold decode_result; rewrite Decoded.
                  ** unfold instruction_value, instruction_opcode, instruction_destination, instruction_left,
                       instruction_right, instruction_immediate, width, cword. rewrite Tag. entailer!.
                  ** decoder_forget output. entailer!.
    }
Qed.
