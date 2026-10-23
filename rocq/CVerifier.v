From VST.floyd Require Import proofauto.
From Stdlib Require Import NArith.
From IceVMC Require Import CProgram.
From IceVM Require Import Syntax State Semantics Interpreter Verifier CIntegers CRepresentation CState CSpecification.
Import ListNotations.
Inductive checked_suffix code : nat -> Prop :=
| checked_end : checked_suffix code (length code)
| checked_instruction p i : decode code p = Some i -> check_at code p = true ->
    checked_suffix code (p + width i) -> checked_suffix code p.
Lemma checked_suffix_complete code p : checked_suffix code p -> forall fuel,
  (length code - p <= fuel)%nat ->
  covers fuel code p = true /\ forallb (check_at code) (scan fuel code p) = true.
Proof.
  intro Checked. induction Checked as [|p i Decoded Check Suffix IH]; intros fuel Space.
  - split.
    + destruct fuel; cbn [covers]; rewrite Nat.eqb_refl; reflexivity.
    + destruct fuel; [reflexivity |]. cbn [scan]. unfold decode. rewrite skipn_all. reflexivity.
  - pose proof (decode_bounds _ _ _ Decoded) as Bounds.
    pose proof (decode_position _ _ _ Decoded) as Position.
    destruct fuel as [|fuel]; [lia |].
    assert (Beyond : (p =? length code)%nat = false) by (apply Nat.eqb_neq; lia).
    specialize (IH fuel ltac:(lia)). destruct IH as [Covered Checks].
    split.
    + cbn [covers]. rewrite Beyond, Decoded. exact Covered.
    + cbn [scan]. rewrite Decoded. cbn [forallb]. rewrite Check. exact Checks.
Qed.
Lemma checked_suffix_accepted code : decode code 0 = Some Entry -> checked_suffix code 0 -> verify code = true.
Proof.
  intros Header Checked. pose proof (checked_suffix_complete code 0 Checked (length code) ltac:(lia)) as [Covered Checks].
  unfold verify, boundaries. rewrite Header, Covered, Checks. reflexivity.
Qed.
Definition checked_prefix code p := checked_suffix code p -> checked_suffix code 0.
Lemma checked_prefix_start code : checked_prefix code 0.
Proof. exact (fun suffix => suffix). Qed.
Lemma checked_prefix_next code p i : checked_prefix code p -> decode code p = Some i -> check_at code p = true ->
  checked_prefix code (p + width i).
Proof. intros Prefix Decoded Check Suffix. apply Prefix. econstructor; eauto. Qed.
Lemma c_byte_eq n : (n < 256)%nat ->
  Int.eq (Int.repr (Z.of_nat n)) (Int.repr 2) = Nat.eqb n 2.
Proof.
  intro Bound. unfold Int.eq. rewrite !Int.unsigned_repr by rep_lia.
  destruct (Coqlib.zeq (Z.of_nat n) 2); destruct (n =? 2)%nat eqn:Test;
    try reflexivity; apply Nat.eqb_eq in Test || apply Nat.eqb_neq in Test; exfalso; lia.
Qed.
Definition verifier_spec : ident * funspec :=
 DECLARE _icevm_verify
 WITH ctx : val, bytes : val, flags : val, owners : val, sh : share, code : list nat, bad : val
 PRE [tptr (Tstruct _icevm_code noattr), tptr tulong]
   PROP () PARAMS (ctx; bad)
   SEP (represents_code sh ctx bytes flags owners code; data_at_ Tsh tulong bad)
 POST [tint] EX accepted : bool,
   PROP (accepted = true -> verify code = true)
   RETURN (Vint (Int.repr (if accepted then 1 else 0)))
   SEP (represents_code sh ctx bytes flags owners code; data_at_ Tsh tulong bad).
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
Lemma body_verifier : semax_body Vprog Gprog f_icevm_verify verifier_spec.
Proof.
  start_function. unfold represents_code, code_fields. Intros.
  forward. forward.
  set (root_post :=
    PROP () LOCAL (lvar _i (Tstruct _icevm_instruction noattr) v_i;
      temp _c ctx; temp _bad bad; temp _p (Vlong Int64.zero);
      temp _t'1 (Vint (Int.repr (if (nth 0 code 0 =? 2)%nat then 0 else 1))))
    SEP (represents_code sh ctx bytes flags owners code; data_at_ Tsh tulong bad;
      data_at_ Tsh (Tstruct _icevm_instruction noattr) v_i)).
  forward_if root_post.
  1: {
    assert (Empty : code = []).
    { apply (f_equal Int64.unsigned) in H2. rewrite Int64.unsigned_repr in H2 by rep_lia.
      rewrite Int64.unsigned_zero in H2. destruct code; auto. cbn [List.length] in H2. lia. }
    subst code. forward. unfold root_post, represents_code, code_fields. entailer!.
  }
  1: {
    assert (Position : (0 < length code)%nat) by
      (destruct code; cbn [List.length]; [contradiction H2; reflexivity | lia]).
    forward. forward.
    1: { entailer!. change (is_int I8 Unsigned (Znth (Z.of_nat 0) (code_values code))).
      rewrite code_values_lookup by exact Position. apply byte_value_typed. eapply code_byte_bound; eauto. }
    change (Znth 0 (code_values code)) with (Znth (Z.of_nat 0) (code_values code)).
    rewrite code_values_lookup by exact Position.
    forward. unfold root_post, represents_code, code_fields. entailer!.
    rewrite c_byte_eq by (eapply code_byte_bound; eauto).
    destruct (nth 0 code 0 =? 2)%nat; reflexivity.
  }
  unfold root_post. Intros. forward_if.
  1: { forward. forward. Exists false. unfold represents_code, code_fields. entailer!. }
  1: {
    assert (Header : (nth 0 code 0 =? 2)%nat = true).
    { change (Int.repr (if (nth 0 code 0 =? 2)%nat then 0 else 1) = Int.zero) in H2.
      destruct (nth 0 code 0 =? 2)%nat; [reflexivity | discriminate]. }
    assert (HeaderDecode : decode code 0 = Some Entry).
    { pose proof (decode_entry_byte code 0) as DecodeHeader. rewrite Header in DecodeHeader.
      destruct (decode code 0) as [i|] eqn:Decoded; [destruct i|]; try discriminate; reflexivity. }
    set (loop_assert := fun p : nat =>
      PROP ((p <= length code)%nat; checked_prefix code p)
      LOCAL (lvar _i (Tstruct _icevm_instruction noattr) v_i;
        temp _c ctx; temp _bad bad; temp _p (Vlong (Int64.repr (Z.of_nat p))))
      SEP (represents_code sh ctx bytes flags owners code; data_at_ Tsh tulong bad;
        data_at_ Tsh (Tstruct _icevm_instruction noattr) v_i)).
    forward_loop (EX p : nat, loop_assert p) break: (loop_assert (length code)).
    1: { Exists 0%nat. unfold loop_assert. entailer!. }
    2: {
      unfold loop_assert. Intros. forward. Exists true.
      unfold represents_code, code_fields. entailer!.
      apply (checked_suffix_accepted code HeaderDecode). apply H4. constructor.
    }
    1: {
      Intros p. unfold loop_assert. Intros. unfold represents_code, code_fields. Intros.
      forward. forward_if.
      2: { assert (Last : p = length code) by lia. subst p. forward. unfold loop_assert, represents_code, code_fields. entailer!. }
      1: {
        assert (Position : (p < length code)%nat) by lia.
        forward. forward_call (sh, ctx, bytes, v_i, code, p).
        destruct (decode code p) as [i|] eqn:Decoded.
        2: {
          unfold decode_result.
          set (bad_decode_post := PROP ()
            LOCAL (lvar _i (Tstruct _icevm_instruction noattr) v_i;
              temp _c ctx; temp _bad bad; temp _p (Vlong (Int64.repr (Z.of_nat p)));
              temp _t'3 (Vint Int.one))
            SEP (represents_code sh ctx bytes flags owners code;
              data_at Tsh tulong (Vlong (Int64.repr (Z.of_nat p))) bad;
              data_at_ Tsh (Tstruct _icevm_instruction noattr) v_i)).
          forward_if bad_decode_post.
          1: { forward. unfold bad_decode_post, represents_code, code_fields. entailer!. }
          1: { contradiction. }
          unfold bad_decode_post. Intros. forward_if; [|discriminate].
          forward. Exists false. unfold represents_code, code_fields. entailer!.
        }
        unfold decode_result.
        set (good_decode_post := PROP ()
          LOCAL (lvar _i (Tstruct _icevm_instruction noattr) v_i;
            temp _c ctx; temp _bad bad; temp _p (Vlong (Int64.repr (Z.of_nat p)));
            temp _t'3 (Vint (Int.repr (if boundary code p then 0 else 1))))
          SEP (represents_code sh ctx bytes flags owners code;
            data_at Tsh tulong (Vlong (Int64.repr (Z.of_nat p))) bad;
            data_at Tsh (Tstruct _icevm_instruction noattr) (instruction_value i) v_i)).
        forward_if good_decode_post.
        1: { discriminate. }
        1: {
          forward_call (sh, ctx, flags, code, p). forward.
          unfold good_decode_post, represents_code, code_fields. entailer!.
          destruct (boundary code p); reflexivity.
        }
        unfold good_decode_post. Intros. forward_if.
        1: {
          sep_apply (data_at_data_at_ Tsh (Tstruct _icevm_instruction noattr) (instruction_value i) v_i).
          forward. Exists false. unfold represents_code, code_fields. entailer!.
        }
        1: {
          assert (Boundary : boundary code p = true) by (destruct (boundary code p); auto; discriminate).
          pose proof (decode_bounds code p i Decoded) as Bounds.
          unfold instruction_value. forward. forward.
          rewrite Int.unsigned_repr by rep_lia. rewrite c_add_repr.
          replace (Z.of_nat p + Z.of_nat (width i)) with (Z.of_nat (p + width i)) by lia.
          forward.
          set (check_post := PROP (check_at code p = true)
            LOCAL (lvar _i (Tstruct _icevm_instruction noattr) v_i;
              temp _c ctx; temp _bad bad; temp _p (Vlong (Int64.repr (Z.of_nat p)));
              temp _n (Vlong (Int64.repr (Z.of_nat (p + width i)))))
            SEP (represents_code sh ctx bytes flags owners code;
              data_at Tsh tulong (Vlong (Int64.repr (Z.of_nat p))) bad;
              data_at Tsh (Tstruct _icevm_instruction noattr) (instruction_value i) v_i)).
          apply semax_seq with check_post.
          2: {
            unfold check_post. Intros. unfold MORE_COMMANDS, abbreviate. forward.
            sep_apply (data_at_data_at_ Tsh (Tstruct _icevm_instruction noattr) (instruction_value i) v_i).
            Exists (p + width i)%nat. unfold loop_assert. entailer!.
            eapply checked_prefix_next; eassumption.
          }
          abbreviate_semax. destruct i.
          1: {
            known_switch. unfold represents_code, code_fields. Intros. forward. forward.
            1: { entailer!. rewrite owner_values_lookup by exact Position. exact I. }
            rewrite owner_values_lookup by exact Position. unfold owner_value. rewrite Boundary. forward_if.
            1: {
              sep_apply (data_at_data_at_ Tsh (Tstruct _icevm_instruction noattr) (instruction_value Halt) v_i).
              forward. Exists false. unfold represents_code, code_fields. entailer!.
            }
            1: {
              assert (OwnerBound : Z.of_nat (owner code p) <= Int64.max_unsigned) by
                (pose proof (owner_bound code p); change (Z.of_nat (owner code p) <= 18446744073709551615); lia).
              assert (OwnerZero : owner code p = 0%nat).
              { apply (f_equal Int64.unsigned) in H7.
                rewrite Int64.unsigned_repr in H7 by rep_lia. rewrite Int64.unsigned_zero in H7. lia. }
              assert (Check : check_at code p = true) by (unfold check_at; rewrite Decoded; cbn; now rewrite OwnerZero).
              forward. unfold check_post, represents_code, code_fields. entailer!.
            }
          }
          1: { known_switch. forward. unfold check_post, represents_code, code_fields.
            entailer!; unfold check_at; rewrite Decoded; reflexivity. }
          2: {
            known_switch. unfold represents_code, code_fields. Intros. forward. forward.
            1: { entailer!. rewrite owner_values_lookup by exact Position. exact I. }
            rewrite owner_values_lookup by exact Position. unfold owner_value. rewrite Boundary. forward_if.
            1: {
              sep_apply (data_at_data_at_ Tsh (Tstruct _icevm_instruction noattr) (instruction_value Ret) v_i).
              forward. Exists false. unfold represents_code, code_fields. entailer!.
            }
            1: {
              assert (OwnerNonzero : owner code p <> 0%nat) by
                (intro Zero; rewrite Zero in H7; first [contradiction H7; reflexivity | discriminate H7]).
              assert (Check : check_at code p = true) by
                (unfold check_at; rewrite Decoded; cbn; apply negb_true_iff; apply Nat.eqb_neq; exact OwnerNonzero).
              forward. unfold check_post, represents_code, code_fields. entailer!.
            }
          }
          14: { known_switch. forward. unfold check_post, represents_code, code_fields.
            entailer!; unfold check_at; rewrite Decoded; reflexivity. }
          12: {
            known_switch. forward.
            pose proof (decode_encodable code p (Jump target) H0 Decoded) as Encodable.
            cbn [Encoding.encodable] in Encodable. apply N.ltb_lt in Encodable.
            apply N2Z.inj_lt in Encodable. rewrite nat_N_Z in Encodable.
            change (Z.of_nat target < 18446744073709551616) in Encodable.
            assert (TargetBound : Z.of_nat target <= Int64.max_unsigned) by
              (change (Z.of_nat target <= 18446744073709551615); lia).
            forward_call (sh, ctx, bytes, flags, owners, code, p, target).
            1: { entailer!. cbn [instruction_immediate]. unfold cword. rewrite nat_N_Z. reflexivity. }
            forward_if.
            1: {
              sep_apply (data_at_data_at_ Tsh (Tstruct _icevm_instruction noattr) (instruction_value (Jump target)) v_i).
              forward. Exists false. unfold represents_code, code_fields. entailer!.
            }
            1: {
              assert (Gate : local_target code p target = true) by
                (destruct (local_target code p target); auto; congruence).
              assert (Check : check_at code p = true) by (unfold check_at; rewrite Decoded; exact Gate).
              forward. unfold check_post, represents_code, code_fields. entailer!.
            }
          }
          12: {
            known_switch. forward.
            pose proof (decode_encodable code p (Branch a target) H0 Decoded) as Encodable.
            cbn [Encoding.encodable] in Encodable. apply andb_true_iff in Encodable. destruct Encodable as [_ Encodable]. apply N.ltb_lt in Encodable.
            apply N2Z.inj_lt in Encodable. rewrite nat_N_Z in Encodable.
            change (Z.of_nat target < 18446744073709551616) in Encodable.
            assert (TargetBound : Z.of_nat target <= Int64.max_unsigned) by
              (change (Z.of_nat target <= 18446744073709551615); lia).
            assert (NextBound : Z.of_nat (p + width (Branch a target)) <= Int64.max_unsigned) by
              (change (Z.of_nat (p + width (Branch a target)) <= 18446744073709551615); lia).
            forward_call (sh, ctx, bytes, flags, owners, code, p, target).
            1: { entailer!. cbn [instruction_immediate]. unfold cword. rewrite nat_N_Z. reflexivity. }
            set (guard_post := PROP ()
              LOCAL (lvar _i (Tstruct _icevm_instruction noattr) v_i;
                temp _c ctx; temp _bad bad; temp _p (Vlong (Int64.repr (Z.of_nat p)));
                temp _n (Vlong (Int64.repr (Z.of_nat (p + width (Branch a target)))));
                temp _t'7 (Vint (Int.repr (if (local_target code p target && local_target code p (p + width (Branch a target)))%bool then 0 else 1))))
              SEP (represents_code sh ctx bytes flags owners code;
                data_at Tsh tulong (Vlong (Int64.repr (Z.of_nat p))) bad;
                data_at Tsh (Tstruct _icevm_instruction noattr) (instruction_value (Branch a target)) v_i)).
            forward_if guard_post.
            1: {
              assert (First : local_target code p target = false) by (destruct (local_target code p target); auto; discriminate).
              forward. unfold guard_post, represents_code, code_fields. rewrite First. cbn [andb]. entailer!.
            }
            1: {
              assert (First : local_target code p target = true) by (destruct (local_target code p target); auto; congruence).
              forward_call (sh, ctx, bytes, flags, owners, code, p, (p + width (Branch a target))%nat). forward.
              unfold guard_post, represents_code, code_fields. rewrite First. cbn [andb]. entailer!.
              destruct (local_target code p (p + width (Branch a target))); reflexivity.
            }
            unfold guard_post. Intros. forward_if.
            1: {
              sep_apply (data_at_data_at_ Tsh (Tstruct _icevm_instruction noattr) (instruction_value (Branch a target)) v_i).
              forward. Exists false. unfold represents_code, code_fields. entailer!.
            }
            1: {
              assert (Gate : (local_target code p target && local_target code p (p + width (Branch a target)))%bool = true).
              { change (Int.repr (if (local_target code p target && local_target code p (p + width (Branch a target)))%bool then 0 else 1) = Int.zero) in H7.
                destruct (local_target code p target && local_target code p (p + width (Branch a target)))%bool; [reflexivity | discriminate]. }
              assert (Check : check_at code p = true) by (unfold check_at; rewrite Decoded; exact Gate).
              forward. unfold check_post, represents_code, code_fields. entailer!.
            }
          }
          12: {
            known_switch. forward.
            pose proof (decode_encodable code p (Call target) H0 Decoded) as Encodable.
            cbn [Encoding.encodable] in Encodable. apply N.ltb_lt in Encodable.
            apply N2Z.inj_lt in Encodable. rewrite nat_N_Z in Encodable.
            change (Z.of_nat target < 18446744073709551616) in Encodable.
            assert (TargetBound : Z.of_nat target <= Int64.max_unsigned) by
              (change (Z.of_nat target <= 18446744073709551615); lia).
            assert (NextBound : Z.of_nat (p + width (Call target)) <= Int64.max_unsigned) by
              (change (Z.of_nat (p + width (Call target)) <= 18446744073709551615); lia).
            forward_call (sh, ctx, bytes, flags, owners, code, target).
            1: { entailer!. cbn [instruction_immediate]. unfold cword. rewrite nat_N_Z. reflexivity. }
            set (guard_post := PROP ()
              LOCAL (lvar _i (Tstruct _icevm_instruction noattr) v_i;
                temp _c ctx; temp _bad bad; temp _p (Vlong (Int64.repr (Z.of_nat p)));
                temp _n (Vlong (Int64.repr (Z.of_nat (p + width (Call target)))));
                temp _t'10 (Vint (Int.repr (if (call_target code target && local_target code p (p + width (Call target)))%bool then 0 else 1))))
              SEP (represents_code sh ctx bytes flags owners code;
                data_at Tsh tulong (Vlong (Int64.repr (Z.of_nat p))) bad;
                data_at Tsh (Tstruct _icevm_instruction noattr) (instruction_value (Call target)) v_i)).
            forward_if guard_post.
            1: {
              assert (First : call_target code target = false) by (destruct (call_target code target); auto; discriminate).
              forward. unfold guard_post, represents_code, code_fields. rewrite First. cbn [andb]. entailer!.
            }
            1: {
              assert (First : call_target code target = true) by (destruct (call_target code target); auto; congruence).
              forward_call (sh, ctx, bytes, flags, owners, code, p, (p + width (Call target))%nat). forward.
              unfold guard_post, represents_code, code_fields. rewrite First. cbn [andb]. entailer!.
              destruct (local_target code p (p + width (Call target))); reflexivity.
            }
            unfold guard_post. Intros. forward_if.
            1: {
              sep_apply (data_at_data_at_ Tsh (Tstruct _icevm_instruction noattr) (instruction_value (Call target)) v_i).
              forward. Exists false. unfold represents_code, code_fields. entailer!.
            }
            1: {
              assert (Gate : (call_target code target && local_target code p (p + width (Call target)))%bool = true).
              { change (Int.repr (if (call_target code target && local_target code p (p + width (Call target)))%bool then 0 else 1) = Int.zero) in H7.
                destruct (call_target code target && local_target code p (p + width (Call target)))%bool; [reflexivity | discriminate]. }
              assert (Check : check_at code p = true) by (unfold check_at; rewrite Decoded; exact Gate).
              forward. unfold check_post, represents_code, code_fields. entailer!.
            }
          }
          all: try (match goal with op : binop |- _ => destruct op end).
          all: known_switch.
          all: lazymatch type of Decoded with decode _ _ = Some ?ins =>
            assert (NextBound : Z.of_nat (p + width ins) <= Int64.max_unsigned) by
              (change (Z.of_nat (p + width ins) <= 18446744073709551615); lia);
            forward_call (sh, ctx, bytes, flags, owners, code, p, (p + width ins)%nat)
          end.
          all: forward_if.
          all: lazymatch goal with
          | |- semax _ _ (Ssequence (Sreturn _) _) _ =>
            lazymatch type of Decoded with decode _ _ = Some ?ins =>
              sep_apply (data_at_data_at_ Tsh (Tstruct _icevm_instruction noattr) (instruction_value ins) v_i);
              forward; Exists false; unfold represents_code, code_fields; entailer!
            end
          | |- semax _ _ (Sreturn _) _ =>
            lazymatch type of Decoded with decode _ _ = Some ?ins =>
              sep_apply (data_at_data_at_ Tsh (Tstruct _icevm_instruction noattr) (instruction_value ins) v_i);
              forward; Exists false; unfold represents_code, code_fields; entailer!
            end
          | _ => idtac
          end.
          all: lazymatch type of Decoded with decode _ _ = Some ?ins =>
            assert (Gate : local_target code p (p + width ins) = true) by
              (change (Int.repr (if local_target code p (p + width ins) then 1 else 0) <> Int.zero) in H7;
               destruct (local_target code p (p + width ins)); [reflexivity | contradiction H7; reflexivity]);
            assert (Check : check_at code p = true) by (unfold check_at; rewrite Decoded; exact Gate);
            forward; unfold check_post, represents_code, code_fields; entailer!
          end.
        }
      }
    }
  }
Qed.
