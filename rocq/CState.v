From VST.floyd Require Import proofauto.
From Stdlib Require Import NArith.
From IceVMC Require Import CProgram.
From IceVM Require Import Syntax State Semantics CIntegers CRepresentation.
Import ListNotations.
Local Opaque memory_size stack_size.
Lemma register_values_update r d v : (d < 16)%nat ->
  register_values (put r d v) = upd_Znth (Z.of_nat d) (register_values r) (Vlong (cword v)).
Proof.
  intro D. apply Znth_eq_ext.
  - rewrite Zlength_upd_Znth, !register_values_length. reflexivity.
  - intros n Bound. rewrite register_values_length in Bound.
    rewrite <- (Z2Nat.id n) by lia.
    rewrite register_values_lookup by lia.
    destruct (Nat.eq_dec (Z.to_nat n) d) as [Same | Different].
    + subst d. rewrite put_same, cword_word, upd_Znth_same by (rewrite register_values_length; lia).
      reflexivity.
    + rewrite put_other by assumption. rewrite upd_Znth_diff by (rewrite ?register_values_length; lia).
      symmetry. apply register_values_lookup. lia.
Qed.
Lemma memory_values_ext m m' :
  (forall n, (n < memory_size)%nat -> m n = m' n) -> memory_values m = memory_values m'.
Proof.
  intro Same. unfold memory_values. apply map_ext_in. intros n Present.
  apply in_seq in Present. rewrite Same by lia. reflexivity.
Qed.
Lemma tabulated_update {A} {default : Inhabitant A} (f : nat -> A) size d v :
  (d < size)%nat ->
  map (fun n => if Nat.eqb n d then v else f n) (seq 0 size) =
  upd_Znth (Z.of_nat d) (map f (seq 0 size)) v.
Proof.
  intro D. apply Znth_eq_ext.
  - rewrite Zlength_upd_Znth, !Zlength_map, !Zlength_correct, !length_seq. reflexivity.
  - intros n Bound. rewrite Zlength_map, Zlength_correct, length_seq in Bound.
    rewrite tabulated_lookup by lia.
    destruct (Nat.eq_dec (Z.to_nat n) d) as [Same | Different].
    + subst d. rewrite Nat.eqb_refl, Z2Nat.id by lia.
      rewrite upd_Znth_same by (rewrite Zlength_map, Zlength_correct, length_seq; lia).
      reflexivity.
    + apply Nat.eqb_neq in Different.
      rewrite Different. rewrite upd_Znth_diff by
        (rewrite ?Zlength_map, ?Zlength_correct, ?length_seq; apply Nat.eqb_neq in Different; lia).
      symmetry. apply tabulated_lookup. lia.
Qed.
Lemma memory_values_update m d v : (d < memory_size)%nat ->
  memory_values (fun n => if Nat.eqb n d then v else m n) =
  upd_Znth (Z.of_nat d) (memory_values m) (Vint (Int.repr (Z.of_N v))).
Proof.
  intro D. unfold memory_values. rewrite <- tabulated_update by exact D.
  apply map_ext. intro n. destruct (Nat.eqb n d); reflexivity.
Qed.
Lemma memory_values_clear_next m lo hi : (lo <= hi < memory_size)%nat ->
  memory_values (clear m lo (S hi)) =
  upd_Znth (Z.of_nat hi) (memory_values (clear m lo hi)) (Vint Int.zero).
Proof.
  intro Bounds. change Int.zero with (Int.repr (Z.of_N 0%N)).
  rewrite <- (memory_values_update (clear m lo hi) hi 0%N) by lia.
  apply memory_values_ext. intros n Position. unfold clear.
  destruct (Nat.eqb n hi) eqn:Same.
  - apply Nat.eqb_eq in Same. subst n.
    assert (Lower : (lo <=? hi)%nat = true) by (apply Nat.leb_le; lia).
    assert (Upper : (hi <? S hi)%nat = true) by (apply Nat.ltb_lt; lia).
    now rewrite Lower, Upper.
  - apply Nat.eqb_neq in Same.
    destruct (lo <=? n)%nat eqn:Lower; cbn [andb]; [|reflexivity].
    destruct (n <? hi)%nat eqn:Upper; destruct (n <? S hi)%nat eqn:Upper'; auto;
      apply Nat.ltb_lt in Upper || apply Nat.ltb_ge in Upper;
      apply Nat.ltb_lt in Upper' || apply Nat.ltb_ge in Upper'; lia.
Qed.
Lemma memory_values_clear_empty m lo : memory_values (clear m lo lo) = memory_values m.
Proof.
  apply memory_values_ext. intros n Position. unfold clear.
  destruct (lo <=? n)%nat eqn:Lower; destruct (n <? lo)%nat eqn:Upper; cbn [andb]; auto.
  apply Nat.leb_le in Lower. apply Nat.ltb_lt in Upper. lia.
Qed.
Lemma cword_low_byte x : (x < modulus)%N ->
  Int.zero_ext 8 (Int64.loword (cword x)) = Int.repr (Z.of_N (N.land x 255)).
Proof.
  intro Bound. rewrite <- (Int.repr_unsigned (Int.zero_ext 8 (Int64.loword (cword x)))).
  rewrite Int.zero_ext_mod by (change (0 <= 8 < 32); lia).
  unfold Int64.loword. rewrite cword_unsigned by assumption.
  rewrite Int.unsigned_repr_eq.
  change (Int.repr ((Z.of_N x mod 4294967296) mod 256) = Int.repr (Z.of_N (N.land x 255))).
  rewrite Z.mod_mod_divide by (exists 16777216; reflexivity).
  rewrite N2Z.inj_land. replace (Z.of_N 255%N) with (Z.ones 8) by reflexivity.
  rewrite Z.land_ones by lia. reflexivity.
Qed.
Lemma cword_shru x k : (x < modulus)%N -> (k < modulus)%N ->
  Int64.shru (cword x) (cword k) = cword (N.shiftr x k).
Proof.
  intros X K. unfold Int64.shru. rewrite !cword_unsigned by assumption.
  unfold cword. now rewrite N2Z.inj_shiftr.
Qed.
Definition store_prefix (m : memory) (a : nat) (v : N) (n : nat) : memory :=
  fun i => if ((a <=? i)%nat && (i <? a + n)%nat)%bool
    then N.land (N.shiftr v (N.of_nat (8 * (i - a)))) 255 else m i.
Lemma store_prefix_complete m a v : store_prefix m a v 8 = write64 m a v.
Proof. reflexivity. Qed.
Lemma memory_values_store_empty m a v : memory_values (store_prefix m a v 0) = memory_values m.
Proof.
  apply memory_values_ext. intros n Position. unfold store_prefix.
  rewrite Nat.add_0_r.
  destruct (a <=? n)%nat eqn:Lower; destruct (n <? a)%nat eqn:Upper; cbn [andb]; auto.
  apply Nat.leb_le in Lower. apply Nat.ltb_lt in Upper. lia.
Qed.
Lemma memory_values_store_next m a v n : (a + n < memory_size)%nat ->
  memory_values (store_prefix m a v (S n)) =
  upd_Znth (Z.of_nat (a + n)) (memory_values (store_prefix m a v n))
    (Vint (Int.repr (Z.of_N (N.land (N.shiftr v (N.of_nat (8 * n))) 255)))).
Proof.
  intro Bounds. rewrite <- memory_values_update by assumption.
  apply memory_values_ext. intros index Position. unfold store_prefix.
  destruct (Nat.eqb index (a + n)) eqn:Same.
  - apply Nat.eqb_eq in Same. subst index.
    assert (Lower : (a <=? a + n)%nat = true) by (apply Nat.leb_le; lia).
    assert (Upper : (a + n <? a + S n)%nat = true) by (apply Nat.ltb_lt; lia).
    rewrite Lower, Upper. cbn [andb]. replace (a + n - a)%nat with n by lia. reflexivity.
  - apply Nat.eqb_neq in Same.
    destruct (a <=? index)%nat eqn:Lower; cbn [andb]; [|reflexivity].
    destruct (index <? a + n)%nat eqn:Upper; destruct (index <? a + S n)%nat eqn:Upper'; auto;
      apply Nat.ltb_lt in Upper || apply Nat.ltb_ge in Upper;
      apply Nat.ltb_lt in Upper' || apply Nat.ltb_ge in Upper'; lia.
Qed.
Lemma local_target_boundary code p t : local_target code p t = true -> boundary code t = true.
Proof.
  unfold local_target. rewrite !andb_true_iff. tauto.
Qed.
Lemma call_target_boundary code t : call_target code t = true -> boundary code t = true.
Proof. rewrite call_target_header, andb_true_iff. tauto. Qed.
Lemma execute_pc_cases code s ins :
  pc (execute code s ins) = pc s \/ pc (execute code s ins) = (pc s + width ins)%nat \/
  boundary code (pc (execute code s ins)) = true.
Proof.
  destruct ins; cbn [execute]; unfold transfer, write_reg, at_pc, finish; cbn;
    repeat match goal with
    | |- context [if ?b then _ else _] => destruct b eqn:?
    | |- context [match ?x with Some _ => _ | None => _ end] => destruct x eqn:?
    | |- context [match frames s with _ => _ end] => destruct (frames s) eqn:?
    end; cbn; auto using local_target_boundary.
  all: try solve [left; reflexivity].
  all: try solve [right; left; reflexivity].
  all: try solve [right; right; assumption].
  all: try solve [right; right; eapply local_target_boundary; eassumption].
  match goal with H : (_ && _)%bool = true |- _ =>
    apply andb_true_iff in H; destruct H end.
  right. right. eauto using call_target_boundary.
Qed.
Lemma execute_pc_bounded code s ins :
  Z.of_nat (length code) <= Int64.max_unsigned ->
  Z.of_nat (pc s) <= Int64.max_unsigned -> decode code (pc s) = Some ins ->
  Z.of_nat (pc (execute code s ins)) <= Int64.max_unsigned.
Proof.
  intros Code Current Decoded. pose proof (decode_bounds _ _ _ Decoded) as Size.
  destruct (execute_pc_cases code s ins) as [Same | [Next | Target]].
  - now rewrite Same.
  - rewrite Next. lia.
  - apply boundary_position in Target. lia.
Qed.
Lemma execute_frames_bounded code s ins :
  Forall (fun f => Z.of_nat (return_pc f) <= Int64.max_unsigned) (frames s) ->
  Z.of_nat (pc s + width ins) <= Int64.max_unsigned ->
  Forall (fun f => Z.of_nat (return_pc f) <= Int64.max_unsigned) (frames (execute code s ins)).
Proof.
  intros Frames Next. destruct ins; cbn [execute]; unfold transfer, write_reg, at_pc, finish; cbn;
    repeat match goal with
    | |- context [if ?b then _ else _] => destruct b eqn:?
    | |- context [match ?x with Some _ => _ | None => _ end] => destruct x eqn:?
    | |- context [match frames s with _ => _ end] => destruct (frames s) eqn:?
    end; cbn in *; auto.
  - inversion Frames. assumption.
Qed.
Lemma tabulated_window {A} {default : Inhabitant A} (f : nat -> A) size lo count :
  (lo + count <= size)%nat ->
  sublist (Z.of_nat lo) (Z.of_nat (lo + count)) (map f (seq 0 size)) =
  map (fun n => f (lo + n)%nat) (seq 0 count).
Proof.
  intro Bounds.
  assert (Length : Zlength (map f (seq 0 size)) = Z.of_nat size)
    by (rewrite Zlength_map, Zlength_correct, length_seq; reflexivity).
  apply Znth_eq_ext.
  - rewrite Zlength_sublist by lia. rewrite Zlength_map, Zlength_correct, length_seq. lia.
  - intros n Position. rewrite Zlength_sublist in Position by lia.
    rewrite Znth_sublist by lia. rewrite !tabulated_lookup by lia.
    f_equal. lia.
Qed.
Lemma z_little_nat bytes : z_little (map Z.of_nat bytes) = Z.of_N (little bytes).
Proof.
  induction bytes as [|b bytes IH]; cbn [map z_little little]; [reflexivity |].
  rewrite N2Z.inj_add, N2Z.inj_mul, nat_N_Z. rewrite <- IH. reflexivity.
Qed.
Definition memory_window (m : memory) a := map (fun n => Z.of_N (m (a + n)%nat)) (seq 0 8).
Lemma memory_window_length m a : Zlength (memory_window m a) = 8.
Proof. unfold memory_window. rewrite Zlength_map, Zlength_correct, length_seq. reflexivity. Qed.
Lemma memory_window_bytes m a : canonical_memory m -> Forall (fun b => 0 <= b <= 255) (memory_window m a).
Proof.
  intro Canonical. unfold memory_window. apply Forall_map, Forall_forall.
  intros n Present. specialize (Canonical (a + n)%nat).
  apply N2Z.inj_lt in Canonical. change (Z.of_N (m (a + n)%nat) < 256) in Canonical.
  split; [apply N2Z.is_nonneg | lia].
Qed.
Lemma memory_values_window m a : (a + 8 <= memory_size)%nat ->
  sublist (Z.of_nat a) (Z.of_nat (a + 8)) (memory_values m) =
  map (fun b => Vint (Int.repr b)) (memory_window m a).
Proof.
  intro Bounds. unfold memory_values, memory_window. rewrite tabulated_window by assumption.
  rewrite map_map. reflexivity.
Qed.
Lemma memory_window_little m a :
  z_little (memory_window m a) = Z.of_N (read64 m a).
Proof.
  unfold read64, memory_window.
  rewrite <- z_little_nat. rewrite !map_map.
  apply f_equal, map_ext. intro n. now rewrite N_nat_Z.
Qed.
Lemma frame_values_pop f fs inactive :
  map frame_value (rev (f :: fs)) ++ inactive =
  map frame_value (rev fs) ++ frame_value f :: inactive.
Proof. cbn [rev]. rewrite map_app. cbn [map]. now rewrite <- app_assoc. Qed.
Lemma frame_values_push f fs old inactive :
  map frame_value (rev (f :: fs)) ++ inactive =
  upd_Znth (Z.of_nat (length fs)) (map frame_value (rev fs) ++ old :: inactive) (frame_value f).
Proof.
  rewrite frame_values_pop, upd_Znth_app2.
  - rewrite Zlength_map, Zlength_correct, length_rev.
    replace (Z.of_nat (length fs) - Z.of_nat (length fs)) with 0 by lia.
    now rewrite upd_Znth0.
  - rewrite Zlength_map, Zlength_correct, length_rev, Zlength_cons.
    pose proof (Zlength_nonneg inactive). lia.
Qed.
Definition copy_prefix {A} (source original : list A) count :=
  sublist 0 count source ++ sublist count (Zlength original) original.
Lemma copy_prefix_start {A} (source original : list A) : copy_prefix source original 0 = original.
Proof. unfold copy_prefix. rewrite sublist_nil, sublist_same by lia. reflexivity. Qed.
Lemma copy_prefix_complete {A} (source original : list A) : Zlength source = Zlength original ->
  copy_prefix source original (Zlength source) = source.
Proof.
  intro Length. unfold copy_prefix. rewrite Length, sublist_nil, sublist_same by lia.
  now rewrite app_nil_r.
Qed.
Lemma copy_prefix_length {A} (source original : list A) count :
  Zlength source = Zlength original -> 0 <= count <= Zlength source ->
  Zlength (copy_prefix source original count) = Zlength original.
Proof.
  intros Length Bounds. unfold copy_prefix. rewrite Zlength_app, !Zlength_sublist by lia. lia.
Qed.
Lemma copy_prefix_next {A} {default : Inhabitant A} (source original : list A) count :
  Zlength source = Zlength original -> 0 <= count < Zlength source ->
  upd_Znth count (copy_prefix source original count) (Znth count source) =
  copy_prefix source original (count + 1).
Proof.
  intros Length Bounds. unfold copy_prefix. list_solve.
Qed.
Definition code_window (code : list nat) a := map Z.of_nat (sublist (Z.of_nat a) (Z.of_nat (a + 8)) code).
Lemma code_window_length code a : (a + 8 <= length code)%nat -> Zlength (code_window code a) = 8.
Proof.
  intro Bounds. unfold code_window. rewrite Zlength_map, Zlength_sublist by (rewrite ?Zlength_correct; lia). lia.
Qed.
Lemma code_window_bytes code a : Forall (fun b => (b < 256)%nat) code ->
  Forall (fun b => 0 <= b <= 255) (code_window code a).
Proof.
  intro Bytes. unfold code_window. apply Forall_map.
  eapply Forall_impl with (P := fun b : nat => (b < 256)%nat);
    [intros n Byte; split; [apply Nat2Z.is_nonneg |]
    |apply Forall_sublist; assumption].
  apply Nat2Z.inj_lt in Byte. change (Z.of_nat n < 256) in Byte. lia.
Qed.
Lemma code_values_window code a :
  sublist (Z.of_nat a) (Z.of_nat (a + 8)) (code_values code) =
  map (fun b => Vint (Int.repr b)) (code_window code a).
Proof. unfold code_values, code_window. rewrite sublist_map, map_map. reflexivity. Qed.
Lemma code_window_little code a :
  z_little (code_window code a) = Z.of_N (little (sublist (Z.of_nat a) (Z.of_nat (a + 8)) code)).
Proof. unfold code_window. apply z_little_nat. Qed.
Lemma c_int_add_repr x y : Int.add (Int.repr x) (Int.repr y) = Int.repr (x + y).
Proof.
  unfold Int.add. apply Int.eqm_samerepr. apply Int.eqm_add;
    apply Int.eqm_sym; apply Int.eqm_unsigned_repr.
Qed.
Lemma c_sub_repr x y : Int64.sub (Int64.repr x) (Int64.repr y) = Int64.repr (x - y).
Proof.
  unfold Int64.sub. apply Int64.eqm_samerepr. apply Int64.eqm_sub;
    apply Int64.eqm_sym; apply Int64.eqm_unsigned_repr.
Qed.
Lemma byte_window_split (sh : share) (n : Z) (values : list val) (base : val) (lo : Z) :
  0 <= lo -> lo + 8 <= n -> Zlength values = n ->
  data_at sh (tarray tuchar n) values base =
  (data_at sh (tarray tuchar lo) (sublist 0 lo values) base *
   data_at sh (tarray tuchar 8) (sublist lo (lo + 8) values)
     (field_address0 (tarray tuchar n) [ArraySubsc lo] base) *
   data_at sh (tarray tuchar (n - (lo + 8))) (sublist (lo + 8) n values)
     (field_address0 (tarray tuchar n) [ArraySubsc (lo + 8)] base))%logic.
Proof.
  intros Lower Upper Length. unfold tarray.
  rewrite (@split3_data_at_Tarray_tuchar CompSpecs sh n lo (lo + 8) values base
    ltac:(split; lia) Upper Length).
  replace (lo + 8 - lo) with 8 by lia. reflexivity.
Qed.
Lemma byte_window_join (sh : share) (n : Z) (values : list val) (base : val) (lo : Z) :
  0 <= lo -> lo + 8 <= n -> Zlength values = n ->
  (data_at sh (tarray tuchar lo) (sublist 0 lo values) base *
   data_at sh (tarray tuchar 8) (sublist lo (lo + 8) values)
     (field_address0 (tarray tuchar n) [ArraySubsc lo] base) *
   data_at sh (tarray tuchar (n - (lo + 8))) (sublist (lo + 8) n values)
     (field_address0 (tarray tuchar n) [ArraySubsc (lo + 8)] base))%logic
  |-- data_at sh (tarray tuchar n) values base.
Proof. intros Lower Upper Length. rewrite (byte_window_split sh n values base lo Lower Upper Length). apply derives_refl. Qed.
Lemma c_le64 x y : 0 <= x <= Int64.max_unsigned -> 0 <= y <= Int64.max_unsigned ->
  Int64.cmpu Cle (Int64.repr x) (Int64.repr y) = (x <=? y)%Z.
Proof.
  intros X Y. cbn [Int64.cmpu]. unfold Int64.ltu. rewrite !Int64.unsigned_repr by lia.
  destruct (Coqlib.zlt y x); destruct (x <=? y)%Z eqn:R; try reflexivity;
    apply Z.leb_le in R || apply Z.leb_gt in R; exfalso; lia.
Qed.
