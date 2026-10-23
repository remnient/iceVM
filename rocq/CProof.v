From VST.floyd Require Import proofauto.
From IceVMC Require Import CProgram.
From IceVM Require Import CRepresentation CIntegers Semantics CSpecification.
Import ListNotations.
Lemma body_trap : semax_body Vprog Gprog f_trap trap_spec.
Proof. start_function. forward. forward. entailer!. Qed.

Lemma body_read64 : semax_body Vprog Gprog f_read64 read64_spec.
Proof.
  start_function. forward.
  forward_for_simple_bound 8
    (EX i : Z, PROP ()
      LOCAL (temp _p p; temp _v (Vlong (Int64.repr (byte_sum contents (Z.to_nat i)))))
      SEP (data_at sh (tarray tuchar 8) (map (fun b => Vint (Int.repr b)) contents) p)).
  - entailer!.
  - assert (Byte : 0 <= Znth i contents <= 255) by (apply Forall_Znth; auto; lia).
    forward. { entailer!. change (Znth i contents <= 255). lia. }
    forward. { entailer!. change (8 * i < 64). lia. }
    entailer!.
    unfold Int64.shl.
    rewrite (Int64.unsigned_repr (Znth i contents)) by (change (0 <= Znth i contents <= 18446744073709551615); lia).
    rewrite (Int64.unsigned_repr (8 * i)) by (change (0 <= 8 * i <= 18446744073709551615); lia).
    rewrite Z.shiftl_mul_pow2 by lia. rewrite c_add_repr.
    replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
    cbn [byte_sum]. now rewrite Z2Nat.id by lia.
  - forward.
Qed.

Lemma body_boundary : semax_body Vprog Gprog f_boundary boundary_spec.
Proof.
  start_function. forward.
  forward_if (PROP () LOCAL (temp _t'1 (boundary_value code p))
    SEP (field_at sh (Tstruct _icevm_code noattr) [StructField _size]
           (Vlong (Int64.repr (Z.of_nat (length code)))) c;
         field_at sh (Tstruct _icevm_code noattr) [StructField _boundary] flags c;
         data_at sh (tarray tuchar (Z.of_nat (length code))) (boundary_values code) flags)).
  - assert (Position : (p < length code)%nat) by rep_lia.
    forward. forward.
    + entailer!. rewrite boundary_values_lookup by assumption.
      unfold boundary_value. destruct (Semantics.boundary code p); vm_compute; discriminate.
    + rewrite boundary_values_lookup by assumption. unfold boundary_value.
      destruct (Semantics.boundary code p) eqn:B; forward; entailer!;
        unfold boundary_value; rewrite B; reflexivity.
  - assert (Position : (length code <= p)%nat) by rep_lia.
    assert (B : Semantics.boundary code p = false).
    { destruct (Semantics.boundary code p) eqn:B; auto. apply boundary_position in B. lia. }
    forward. entailer!. unfold boundary_value. now rewrite B.
  - forward.
Qed.

Lemma c_nat_eq n m : Z.of_nat n <= Int64.max_unsigned -> Z.of_nat m <= Int64.max_unsigned ->
  Int64.eq (Int64.repr (Z.of_nat n)) (Int64.repr (Z.of_nat m)) = Nat.eqb n m.
Proof.
  intros N M. unfold Int64.eq. rewrite !Int64.unsigned_repr by lia.
  destruct (Coqlib.zeq (Z.of_nat n) (Z.of_nat m)); destruct (Nat.eqb n m) eqn:E; auto;
    apply Nat.eqb_eq in E || apply Nat.eqb_neq in E; exfalso; lia.
Qed.
Lemma body_local : semax_body Vprog Gprog f_local local_spec.
Proof.
  start_function. unfold represents_code, code_fields. Intros.
  forward_call (sh, c, flags, code, p). unfold boundary_value.
  forward_if (PROP ()
    LOCAL (temp _t'2 (Vint (Int.repr (if local_boundaries code p t then 1 else 0))); temp _c c;
      temp _p (Vlong (Int64.repr (Z.of_nat p))); temp _t (Vlong (Int64.repr (Z.of_nat t))))
    SEP (represents_code sh c bytes flags owners code)).
  - assert (Bp : Semantics.boundary code p = true).
    { destruct (Semantics.boundary code p) eqn:B; auto; congruence. }
    forward_call (sh, c, flags, code, t).
    unfold boundary_value. destruct (Semantics.boundary code t) eqn:Bt; forward;
      unfold represents_code, code_fields; entailer!; unfold local_boundaries; rewrite Bp, Bt; reflexivity.
  - assert (Bp : Semantics.boundary code p = false).
    { destruct (Semantics.boundary code p) eqn:B; auto; exfalso; discriminate. }
    forward. unfold represents_code, code_fields. entailer!. unfold local_boundaries. now rewrite Bp.
  - unfold represents_code, code_fields. Intros.
    forward_if (PROP ()
      LOCAL (temp _t'4 (Vint (Int.repr (if local_target code p t then 1 else 0))))
      SEP (represents_code sh c bytes flags owners code)).
    + assert (Gate : local_boundaries code p t = true).
      { destruct (local_boundaries code p t) eqn:G; auto; congruence. }
      unfold local_boundaries in Gate. apply andb_true_iff in Gate. destruct Gate as [Bp Bt].
      assert (From : (p < length code)%nat) by (now apply boundary_position).
      assert (To : (t < length code)%nat) by (now apply boundary_position).
      forward. forward.
      { entailer!. rewrite owner_values_lookup by assumption. unfold owner_value. exact I. }
      rewrite owner_values_lookup by assumption. unfold owner_value. rewrite Bp.
      forward. forward.
      { entailer!. rewrite owner_values_lookup by assumption. unfold owner_value. exact I. }
      rewrite owner_values_lookup by assumption. unfold owner_value. rewrite Bt.
      assert (OwnerP : Z.of_nat (owner code p) <= Int64.max_unsigned).
      { change (Z.of_nat (owner code p) <= 18446744073709551615). pose proof (owner_bound code p). lia. }
      assert (OwnerT : Z.of_nat (owner code t) <= Int64.max_unsigned).
      { change (Z.of_nat (owner code t) <= 18446744073709551615). pose proof (owner_bound code t). lia. }
      forward. unfold represents_code, code_fields. entailer!.
      unfold local_target. rewrite Bp, Bt. cbn [andb].
      destruct (Coqlib.zeq (Z.of_nat (owner code p)) (Z.of_nat (owner code t)));
        destruct (Nat.eqb (owner code p) (owner code t)) eqn:E; try reflexivity;
        apply Nat.eqb_eq in E || apply Nat.eqb_neq in E; exfalso; lia.
    + assert (Gate : local_boundaries code p t = false).
      { destruct (local_boundaries code p t) eqn:G; auto; discriminate. }
      forward. unfold represents_code, code_fields. entailer!.
      unfold local_target. fold (local_boundaries code p t). now rewrite Gate.
    + forward.
Qed.
Lemma body_callable : semax_body Vprog Gprog f_callable callable_spec.
Proof.
  start_function. unfold represents_code, code_fields. Intros.
  forward_if (PROP ()
    LOCAL (temp _t'1 (Vint (Int.repr (if call_boundary code t then 1 else 0)));
      temp _c c; temp _t (Vlong (Int64.repr (Z.of_nat t))))
    SEP (represents_code sh c bytes flags owners code)).
  - assert (Zero : Nat.eqb t 0 = false) by (apply Nat.eqb_neq; intro Zero; subst t; contradiction).
    forward_call (sh, c, flags, code, t).
    unfold boundary_value. destruct (Semantics.boundary code t) eqn:B; forward;
      unfold represents_code, code_fields; entailer!; unfold call_boundary; rewrite Zero, B; reflexivity.
  - apply (f_equal Int64.unsigned) in H3.
    rewrite !Int64.unsigned_repr in H3 by lia. rewrite Int64.unsigned_zero in H3.
    assert (Zero : t = 0%nat) by lia. subst t.
    forward. unfold represents_code, code_fields. entailer!; unfold call_boundary; reflexivity.
  - unfold represents_code, code_fields. Intros.
    forward_if (PROP ()
      LOCAL (temp _t'3 (Vint (Int.repr (if call_entry code t then 1 else 0)));
        temp _c c; temp _t (Vlong (Int64.repr (Z.of_nat t))))
      SEP (represents_code sh c bytes flags owners code)).
    + assert (Gate : call_boundary code t = true).
      { destruct (call_boundary code t) eqn:G; auto; congruence. }
      pose proof Gate as GateTrue. unfold call_boundary in Gate.
      apply andb_true_iff in Gate. destruct Gate as [Nonzero Boundary].
      assert (To : (t < length code)%nat) by (now apply boundary_position).
      assert (ByteBound : (nth t code 0%nat < 256)%nat) by (eapply code_byte_bound; eauto).
      forward. forward.
      { entailer!. rewrite code_values_lookup by assumption. now apply byte_value_typed. }
      rewrite code_values_lookup by assumption.
      forward. unfold represents_code, code_fields. entailer!.
      unfold call_entry. rewrite GateTrue. cbn [andb].
      destruct (Coqlib.zeq (Z.of_nat (nth t code 0%nat)) 2);
        destruct (Nat.eqb (nth t code 0%nat) 2) eqn:E; try reflexivity;
        apply Nat.eqb_eq in E || apply Nat.eqb_neq in E; exfalso; lia.
    + assert (Gate : call_boundary code t = false).
      { destruct (call_boundary code t) eqn:G; auto; discriminate. }
      forward. unfold represents_code, code_fields. entailer!.
      unfold call_entry. now rewrite Gate.
    + unfold represents_code, code_fields. Intros.
      forward_if (PROP ()
        LOCAL (temp _t'4 (Vint (Int.repr (if call_target code t then 1 else 0))))
        SEP (represents_code sh c bytes flags owners code)).
      * assert (Entry : call_entry code t = true).
        { destruct (call_entry code t) eqn:E; auto; congruence. }
        pose proof Entry as Original. unfold call_entry, call_boundary in Entry.
        apply andb_true_iff in Entry. destruct Entry as [Prefix Tag].
        apply andb_true_iff in Prefix. destruct Prefix as [Nonzero Boundary].
        assert (To : (t < length code)%nat) by (now apply boundary_position).
        forward. forward.
        { entailer!. rewrite owner_values_lookup by assumption. unfold owner_value. exact I. }
        rewrite owner_values_lookup by assumption. unfold owner_value. rewrite Boundary.
        assert (Owner : Z.of_nat (owner code t) <= Int64.max_unsigned).
        { change (Z.of_nat (owner code t) <= 18446744073709551615). pose proof (owner_bound code t). lia. }
        forward. unfold represents_code, code_fields. entailer!.
        rewrite call_guard_result, Original. cbn [andb].
        change (Vint (Int.repr (if negb (Nat.eqb (owner code t) 0) then 1 else 0)) =
          bool2val (negb (Int64.eq (Int64.repr (Z.of_nat (owner code t))) (Int64.repr (Z.of_nat 0))))).
        rewrite (c_nat_eq (owner code t) 0) by lia.
        destruct (Nat.eqb (owner code t) 0); reflexivity.
      * assert (Entry : call_entry code t = false).
        { destruct (call_entry code t) eqn:E; auto; discriminate. }
        forward. unfold represents_code, code_fields. entailer!.
        rewrite call_guard_result, Entry. reflexivity.
      * forward.
Qed.
