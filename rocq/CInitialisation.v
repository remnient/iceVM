From VST.floyd Require Import proofauto.
From Stdlib Require Import NArith.
From IceVMC Require Import CProgram.
From IceVM Require Import Syntax State Semantics CIntegers CRepresentation CState CSpecification CMetadata.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope logic.
Definition cache_type (word : bool) (count : Z) := if word then tarray tulong count else tarray tuchar count.
Definition cache_data (word : bool) (count : Z) (values : list val) p : mpred :=
  if word then data_at Tsh (tarray tulong count) values p else data_at Tsh (tarray tuchar count) values p.
Definition cache_zero word count p :=
  cache_data word count (map (fun _ : nat => if word then Vlong Int64.zero else Vint Int.zero)
    (seq 0 (Z.to_nat count))) p.
Lemma allocation_size_guard z : 0 <= z <= 4294967295 ->
  Int64.ltu (Int64.divu (Int64.repr (-1)) (Int64.repr 8)) (Int64.repr z) = false.
Proof.
  intro Bound. change (Int64.ltu (Int64.repr 2305843009213693951) (Int64.repr z) = false).
  unfold Int64.ltu. rewrite !Int64.unsigned_repr by rep_lia.
  destruct (Coqlib.zlt 2305843009213693951 z); [lia | reflexivity].
Qed.
Section Allocation.
Context (allocation_token : type -> val -> mpred).
Definition calloc_result word count p : mpred :=
  if eq_dec p nullval then emp else allocation_token (cache_type word count) p * cache_zero word count p.
Lemma calloc_result_block word count p : calloc_result word count p |-- allocation_block allocation_token (cache_type word count) p.
Proof.
  unfold calloc_result, allocation_block. destruct (eq_dec p nullval); [apply derives_refl |].
  destruct word; unfold cache_zero, cache_data, cache_type;
    sep_apply data_at_data_at_; cancel.
Qed.
Definition calloc_spec : ident * funspec :=
 DECLARE _calloc
 WITH word : bool, count : Z
 PRE [tulong, tulong]
   PROP (0 < count; count * (if word then 8 else 1) <= Ptrofs.max_unsigned)
   PARAMS (Vlong (Int64.repr count); Vlong (Int64.repr (if word then 8 else 1))) SEP ()
 POST [tptr tvoid] EX p : val,
   PROP (is_pointer_or_null p) RETURN (p) SEP (calloc_result word count p).
Definition metadata_slots (code : list nat) := Nat.max 1 (length code).
Definition metadata_count code := Z.of_nat (metadata_slots code).
Lemma metadata_count_empty code : length code = O -> metadata_count code = 1.
Proof. intro Empty. unfold metadata_count, metadata_slots. now rewrite Empty. Qed.
Lemma metadata_count_nonempty code : (0 < length code)%nat -> metadata_count code = Z.of_nat (length code).
Proof. intro Nonempty. unfold metadata_count, metadata_slots. now rewrite Nat.max_r by lia. Qed.
Lemma metadata_count_bounds code : Z.of_nat (length code) <= 4294967295 -> 1 <= metadata_count code <= 4294967295.
Proof.
  intro Bound. destruct (Nat.eq_dec (length code) O) as [Empty | Nonempty].
  - rewrite metadata_count_empty by exact Empty. lia.
  - rewrite metadata_count_nonempty by lia. lia.
Qed.
Definition allocation_failed flags owners :=
  if eq_dec flags nullval then true else if eq_dec owners nullval then true else false.
Definition code_storage ctx bytes flags owners code : mpred :=
  field_at Tsh (Tstruct _icevm_code noattr) [StructField _bytes] bytes ctx *
  field_at Tsh (Tstruct _icevm_code noattr) [StructField _size] (Vlong (Int64.repr (Z.of_nat (length code)))) ctx *
  field_at Tsh (Tstruct _icevm_code noattr) [StructField _boundary] flags ctx *
  field_at Tsh (Tstruct _icevm_code noattr) [StructField _owner] owners ctx *
  data_at Tsh (tarray tuchar (Z.of_nat (length code))) (code_values code) bytes.
Definition initialized_code ctx bytes flags owners code : mpred :=
  !! (Z.of_nat (length code) <= 4294967295 /\ Forall (fun b => (b < 256)%nat) code /\ flags <> nullval /\ owners <> nullval) &&
  (code_storage ctx bytes flags owners code *
   cache_data false (metadata_count code) (map (boundary_value code) (seq 0 (metadata_slots code))) flags *
   cache_data true (metadata_count code) (map (owner_value code) (seq 0 (metadata_slots code))) owners *
   allocation_token (cache_type false (metadata_count code)) flags *
   allocation_token (cache_type true (metadata_count code)) owners).
Definition init_spec : ident * funspec :=
 DECLARE _icevm_code_init
 WITH ctx : val, bytes : val, code : list nat
 PRE [tptr (Tstruct _icevm_code noattr), tptr tuchar, tulong]
   PROP (Forall (fun b => (b < 256)%nat) code; Z.of_nat (length code) <= Int64.max_unsigned)
   PARAMS (ctx; bytes; Vlong (Int64.repr (Z.of_nat (length code))))
   SEP (data_at_ Tsh (Tstruct _icevm_code noattr) ctx;
     data_at Tsh (tarray tuchar (Z.of_nat (length code))) (code_values code) bytes)
 POST [tint] EX success : bool,
   PROP () RETURN (Vint (Int.repr (if success then 1 else 0)))
   SEP (if success then EX flags : val, EX owners : val, initialized_code ctx bytes flags owners code
     else code_storage ctx bytes nullval nullval code).
Definition init_Gprog := [calloc_spec; free_metadata_spec allocation_token; destroy_spec allocation_token; init_spec] ++ Gprog.
Lemma body_init : semax_body Vprog init_Gprog f_icevm_code_init init_spec.
Proof.
  start_function. forward. forward. forward. forward.
  match goal with |- context [data_at Tsh (Tstruct _icevm_code noattr) ?fields ?pointer] =>
    unfold_data_at (@data_at CompSpecs Tsh (Tstruct _icevm_code noattr) fields pointer)
  end.
  set (size_post := PROP ()
    LOCAL (lvar _i (Tstruct _icevm_instruction noattr) v_i; temp _c ctx; temp _bytes bytes;
      temp _size (Vlong (Int64.repr (Z.of_nat (length code))));
      temp _t'1 (Vint (Int.repr (if (Z.of_nat (length code) <=? 4294967295)%Z then 0 else 1))))
    SEP (code_storage ctx bytes nullval nullval code;
      data_at_ Tsh (Tstruct _icevm_instruction noattr) v_i)).
  forward_if size_post.
  1: {
    change (4294967295 < Z.of_nat (length code)) in H1.
    assert (Rejected : (Z.of_nat (length code) <=? 4294967295)%Z = false) by (apply Z.leb_gt; exact H1).
    forward. unfold size_post, code_storage. rewrite Rejected. entailer!.
  }
  1: {
    assert (Length : Z.of_nat (length code) <= 4294967295) by rep_lia.
    assert (Accepted : (Z.of_nat (length code) <=? 4294967295)%Z = true) by (apply Z.leb_le; exact Length).
    forward. unfold size_post, code_storage. rewrite Accepted. entailer!.
    change (Vint (Int.repr 0) = bool2val
      (Int64.ltu (Int64.divu (Int64.repr (-1)) (Int64.repr 8)) (Int64.repr (Z.of_nat (length code))))).
    rewrite allocation_size_guard by lia. reflexivity.
  }
  unfold size_post. Intros. forward_if.
  1: { forward. Exists false. unfold code_storage. entailer!. }
  1: {
    assert (Length : Z.of_nat (length code) <= 4294967295).
    { apply Z.leb_le.
      change (Int.repr (if (Z.of_nat (length code) <=? 4294967295)%Z then 0 else 1) = Int.zero) in H1.
      destruct (Z.of_nat (length code) <=? 4294967295)%Z; [reflexivity | discriminate]. }
    unfold code_storage. Intros.
    pose proof (metadata_count_bounds code Length) as Count.
    set (count_post := PROP ()
      LOCAL (lvar _i (Tstruct _icevm_instruction noattr) v_i; temp _c ctx; temp _bytes bytes;
        temp _size (Vlong (Int64.repr (Z.of_nat (length code))));
        temp _t'2 (Vlong (Int64.repr (metadata_count code))))
      SEP (code_storage ctx bytes nullval nullval code;
        data_at_ Tsh (Tstruct _icevm_instruction noattr) v_i)).
    forward_if count_post.
    1: {
      assert (Nonempty : (0 < length code)%nat) by (destruct code; cbn [List.length]; [contradiction H2; reflexivity | lia]).
      forward. unfold count_post, code_storage. rewrite metadata_count_nonempty by exact Nonempty. entailer!.
    }
    1: {
      assert (Empty : length code = O).
      { apply (f_equal Int64.unsigned) in H2. rewrite Int64.unsigned_repr in H2 by rep_lia.
        rewrite Int64.unsigned_zero in H2. lia. }
      forward. unfold count_post, code_storage. rewrite metadata_count_empty by exact Empty. entailer!.
    }
    unfold count_post. Intros.
    forward_call (false, metadata_count code).
    Intros flags. unfold code_storage. Intros. forward.
    set (owner_count_post := PROP ()
      LOCAL (lvar _i (Tstruct _icevm_instruction noattr) v_i; temp _c ctx; temp _bytes bytes;
        temp _size (Vlong (Int64.repr (Z.of_nat (length code))));
        temp _t'4 (Vlong (Int64.repr (metadata_count code))))
      SEP (code_storage ctx bytes flags nullval code; calloc_result false (metadata_count code) flags;
        data_at_ Tsh (Tstruct _icevm_instruction noattr) v_i)).
    forward_if owner_count_post.
    1: {
      assert (Nonempty : (0 < length code)%nat) by (destruct code; cbn [List.length]; [match goal with Size : Int64.repr _ <> Int64.zero |- _ => contradiction Size; reflexivity end | lia]).
      forward. unfold owner_count_post, code_storage. rewrite metadata_count_nonempty by exact Nonempty. entailer!.
    }
    1: {
      assert (Empty : length code = O).
      { match goal with Size : Int64.repr _ = Int64.zero |- _ =>
          apply (f_equal Int64.unsigned) in Size; rewrite Int64.unsigned_repr in Size by rep_lia;
          rewrite Int64.unsigned_zero in Size; lia end. }
      forward. unfold owner_count_post, code_storage. rewrite metadata_count_empty by exact Empty. entailer!.
    }
    unfold owner_count_post. Intros. forward_call (true, metadata_count code).
    Intros owners. unfold code_storage. Intros. forward. forward.
    set (allocation_post := PROP ()
      LOCAL (lvar _i (Tstruct _icevm_instruction noattr) v_i; temp _c ctx; temp _bytes bytes;
        temp _size (Vlong (Int64.repr (Z.of_nat (length code))));
        temp _t'6 (Vint (Int.repr (if allocation_failed flags owners then 1 else 0))))
      SEP (code_storage ctx bytes flags owners code;
        calloc_result false (metadata_count code) flags; calloc_result true (metadata_count code) owners;
        data_at_ Tsh (Tstruct _icevm_instruction noattr) v_i)).
    forward_if allocation_post.
    1: { unfold calloc_result, cache_zero, cache_data.
      destruct (eq_dec flags nullval); [subst flags; entailer! | entailer!]. }
    1: { forward. unfold allocation_post, allocation_failed, code_storage.
      destruct (eq_dec flags nullval); [entailer! | contradiction]. }
    1: {
      forward. forward.
      1: {
        unfold calloc_result, cache_zero, cache_data.
        destruct (eq_dec flags nullval); destruct (eq_dec owners nullval); subst; entailer!.
      }
      unfold allocation_post, allocation_failed, code_storage.
      destruct (eq_dec flags nullval); [contradiction |].
      destruct (eq_dec owners nullval) as [Null | Nonnull].
      - subst owners. entailer!.
      - destruct owners; try contradiction; try contradiction PNowners; entailer!.
        unfold is_pointer_or_null in PNowners. simpl in PNowners. subst i.
        exfalso. apply Nonnull. reflexivity.
    }
    unfold allocation_post. Intros. forward_if.
    1: {
      unfold code_storage. Intros.
      sep_apply (calloc_result_block false (metadata_count code) flags).
      sep_apply (calloc_result_block true (metadata_count code) owners).
      forward_call (ctx, flags, owners, cache_type false (metadata_count code), cache_type true (metadata_count code)).
      forward. Exists false. unfold code_storage. entailer!.
    }
    1: {
      assert (Nonflags : flags <> nullval).
      { unfold allocation_failed in H2. destruct (eq_dec flags nullval); [discriminate H2 | assumption]. }
      assert (Nonowners : owners <> nullval).
      { unfold allocation_failed in H2. destruct (eq_dec flags nullval); [discriminate H2 |].
        destruct (eq_dec owners nullval); [discriminate H2 | assumption]. }
      unfold calloc_result. destruct (eq_dec flags nullval); [contradiction |].
      destruct (eq_dec owners nullval); [contradiction |].
      unfold code_storage, cache_zero. Intros. forward. forward.
      set (pending := fun (p current : nat) (flagtable ownertable : nat -> val) =>
        (forall q, metadata_install (metadata_entries (length code - p) code p current)
          (fun _ => Vint Int.one) flagtable q = boundary_value code q) /\
        (forall q, metadata_install (metadata_entries (length code - p) code p current)
          (fun own => Vlong (Int64.repr (Z.of_nat own))) ownertable q = owner_value code q)).
      set (loop_assert := fun (p current : nat) (flagtable ownertable : nat -> val) =>
        PROP ((current <= p <= length code)%nat; pending p current flagtable ownertable)
        LOCAL (lvar _i (Tstruct _icevm_instruction noattr) v_i; temp _c ctx;
          temp _p (Vlong (Int64.repr (Z.of_nat p))); temp _owner (Vlong (Int64.repr (Z.of_nat current))))
        SEP (code_storage ctx bytes flags owners code;
          allocation_token (cache_type false (metadata_count code)) flags;
          allocation_token (cache_type true (metadata_count code)) owners;
          cache_data false (metadata_count code) (map flagtable (seq 0 (metadata_slots code))) flags;
          cache_data true (metadata_count code) (map ownertable (seq 0 (metadata_slots code))) owners;
          data_at_ Tsh (Tstruct _icevm_instruction noattr) v_i)).
      set (loop_exit := PROP () LOCAL (lvar _i (Tstruct _icevm_instruction noattr) v_i)
        SEP (initialized_code ctx bytes flags owners code; data_at_ Tsh (Tstruct _icevm_instruction noattr) v_i)).
      forward_loop (EX p : nat, EX current : nat, EX flagtable : nat -> val, EX ownertable : nat -> val,
        loop_assert p current flagtable ownertable) break: loop_exit.
      1: {
        Exists O O (fun _ : nat => Vint Int.zero) (fun _ : nat => Vlong Int64.zero).
        unfold loop_assert, code_storage. entailer!.
        - unfold pending. rewrite Nat.sub_0_r. split.
          + apply metadata_installed_boundary.
          + apply metadata_installed_owner.
        - unfold metadata_count. rewrite Nat2Z.id. cancel.
      }
      2: { unfold loop_exit. Intros. forward. Exists true flags owners. entailer!. }
      1: {
        Intros p current flagtable ownertable. unfold loop_assert, code_storage. Intros.
        forward_call (Tsh, ctx, bytes, v_i, code, p).
        destruct (decode code p) as [ins |] eqn:Decoded; unfold decode_result.
        2: {
          assert (Finished : metadata_entries (length code - p) code p current = []).
          { destruct (length code - p)%nat; [reflexivity | cbn [metadata_entries]; now rewrite Decoded]. }
          unfold pending in H5. rewrite Finished in H5. cbn [metadata_install] in H5.
          destruct H5 as [Flags Owners].
          assert (SameFlags : map flagtable (seq 0 (metadata_slots code)) = map (boundary_value code) (seq 0 (metadata_slots code)))
            by (apply map_ext; exact Flags).
          assert (SameOwners : map ownertable (seq 0 (metadata_slots code)) = map (owner_value code) (seq 0 (metadata_slots code)))
            by (apply map_ext; exact Owners).
          rewrite SameFlags, SameOwners.
          forward_if.
          1: contradiction.
          forward. unfold loop_exit, initialized_code, code_storage. entailer!.
        }
        1: {
          pose proof (decode_bounds code p ins Decoded) as WidthBound.
          pose proof (decode_position code p ins Decoded) as Position.
          pose proof (instruction_width_positive ins) as Positive.
          forward_if; [|discriminate]. forward. cbn [instruction_value].
          assert (EntryTest : Int.eq (Int.repr (Z.of_nat (instruction_opcode ins))) (Int.repr 2) =
            match ins with Entry => true | _ => false end).
          { destruct ins; try match goal with op : binop |- _ => destruct op end; reflexivity. }
          set (next_owner := match ins with Entry => p | _ => current end).
          set (owner_post := PROP ()
            LOCAL (lvar _i (Tstruct _icevm_instruction noattr) v_i; temp _c ctx;
              temp _p (Vlong (Int64.repr (Z.of_nat p))); temp _owner (Vlong (Int64.repr (Z.of_nat next_owner))))
            SEP (code_storage ctx bytes flags owners code;
              allocation_token (cache_type false (metadata_count code)) flags;
              allocation_token (cache_type true (metadata_count code)) owners;
              cache_data false (metadata_count code) (map flagtable (seq 0 (metadata_slots code))) flags;
              cache_data true (metadata_count code) (map ownertable (seq 0 (metadata_slots code))) owners;
              data_at Tsh (Tstruct _icevm_instruction noattr) (instruction_value ins) v_i)).
          forward_if owner_post.
          1: {
            rewrite H7, Int.eq_true in EntryTest.
            assert (Own : next_owner = p) by (unfold next_owner; destruct ins; try discriminate; reflexivity).
            forward. unfold owner_post, code_storage. rewrite Own. entailer!.
          }
          1: {
            rewrite (Int.eq_false _ _ H7) in EntryTest.
            assert (Own : next_owner = current) by (unfold next_owner; destruct ins; try discriminate; reflexivity).
            forward. unfold owner_post, code_storage. rewrite Own. entailer!.
          }
          unfold owner_post, code_storage, cache_data. Intros. forward. forward.
          1: { rewrite metadata_count_nonempty by lia. entailer!. }
          forward. forward.
          1: { rewrite metadata_count_nonempty by lia. entailer!. }
          forward. cbn [instruction_value]. forward.
          sep_apply (data_at_data_at_ Tsh (Tstruct _icevm_instruction noattr) (instruction_value ins) v_i).
          Exists (p + width ins)%nat next_owner (metadata_set flagtable p (Vint Int.one))
            (metadata_set ownertable p (Vlong (Int64.repr (Z.of_nat next_owner)))).
          unfold loop_assert, code_storage, cache_data. rewrite Int.unsigned_repr by rep_lia.
          assert (OwnBound : (next_owner <= p)%nat) by (unfold next_owner; destruct ins; lia).
          assert (Slot : (p < metadata_slots code)%nat) by
            (unfold metadata_slots; pose proof (Nat.le_max_r 1 (length code)); lia).
          rewrite !metadata_tabulate_set by exact Slot.
          change (Int.zero_ext 8 (Int.repr 1)) with Int.one. entailer!.
          unfold pending in *. rewrite (metadata_advance code p current ins Decoded) in H5.
          rewrite Nat2Z.inj_add. split; [exact H5 | reflexivity].
        }
      }
    }
  }
Qed.
End Allocation.

Section View.
Context (allocation_token : type -> val -> mpred).
Definition cache_remainder code flags owners : mpred :=
  if Nat.eq_dec (length code) O then
    cache_data false 1 (map (boundary_value code) [O]) flags *
    cache_data true 1 (map (owner_value code) [O]) owners
  else emp.
Lemma initialized_code_view ctx bytes flags owners code :
  initialized_code allocation_token ctx bytes flags owners code |--
  represents_code Tsh ctx bytes flags owners code * cache_remainder code flags owners *
  allocation_token (cache_type false (metadata_count code)) flags *
  allocation_token (cache_type true (metadata_count code)) owners.
Proof.
  unfold initialized_code. Intros.
  destruct (Nat.eq_dec (length code) O) as [Empty | Nonempty].
  - assert_PROP (isptr flags /\ isptr owners) as Pointers by (unfold cache_data; entailer!).
    unfold represents_code, code_fields, code_storage, cache_remainder, boundary_values, owner_values.
    rewrite Empty. cbn [seq map].
    destruct (Nat.eq_dec O O); [|contradiction].
    rewrite (data_at_zero_array_eq Tsh tuchar [] flags) by (try reflexivity; tauto).
    rewrite (data_at_zero_array_eq Tsh tulong [] owners) by (try reflexivity; tauto).
    unfold metadata_count, metadata_slots. rewrite Empty. cbn [seq map cache_data]. entailer!.
  - assert (Slots : metadata_slots code = length code) by
      (unfold metadata_slots; rewrite Nat.max_r by lia; reflexivity).
    unfold represents_code, code_fields, code_storage, cache_remainder.
    destruct (Nat.eq_dec (length code) O); [contradiction |].
    unfold cache_data, metadata_count, boundary_values, owner_values. rewrite Slots. entailer!.
Qed.
End View.
