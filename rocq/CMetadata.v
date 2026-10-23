From VST.floyd Require Import proofauto.
From Stdlib Require Import List NArith Arith Bool Lia.
From IceVMC Require Import CProgram.
From IceVM Require Import Syntax Semantics CIntegers CRepresentation CState CSpecification.
Import ListNotations.
Local Open Scope nat_scope.
Fixpoint metadata_entries (fuel : nat) code p current : list (nat * nat) :=
  match fuel with
  | O => []
  | S fuel => match decode code p with
    | None => []
    | Some i => let own := match i with Entry => p | _ => current end in
        (p, own) :: metadata_entries fuel code (p + width i) own
    end
  end.
Lemma metadata_positions fuel code p current :
  map fst (metadata_entries fuel code p current) = scan fuel code p.
Proof.
  revert p current. induction fuel; intros p current; cbn [metadata_entries scan]; auto.
  destruct (decode code p); cbn [map]; auto. f_equal. apply IHfuel.
Qed.
Lemma metadata_lower_bound fuel code p current q own :
  In (q, own) (metadata_entries fuel code p current) -> (p <= q)%nat.
Proof.
  revert p current. induction fuel; intros p current Member; [contradiction |].
  cbn [metadata_entries] in Member. destruct (decode code p) as [i|]; [|contradiction].
  destruct Member as [Same | Member].
  - inversion Same. lia.
  - specialize (IHfuel _ _ Member). lia.
Qed.
Lemma instruction_width_positive i : (0 < width i)%nat.
Proof. destruct i; cbn [width]; lia. Qed.
Lemma metadata_inside fuel code p current q own :
  In (q, own) (metadata_entries fuel code p current) -> (q < length code)%nat.
Proof.
  revert p current. induction fuel; intros p current Member; [contradiction |].
  cbn [metadata_entries] in Member. destruct (decode code p) as [i|] eqn:Decoded; [|contradiction].
  destruct Member as [Same | Member].
  - inversion Same; subst. eapply decode_position; eauto.
  - eapply IHfuel; eauto.
Qed.
Lemma metadata_owner fuel code p current q own :
  In (q, own) (metadata_entries fuel code p current) -> owner_at fuel code p current q = own.
Proof.
  revert p current. induction fuel; intros p current Member; [contradiction |].
  cbn [metadata_entries] in Member. destruct (decode code p) as [i|] eqn:Decoded; [|contradiction].
  cbn [owner_at]. rewrite Decoded. destruct Member as [Same | Member].
  - inversion Same; subst. rewrite Nat.leb_refl. reflexivity.
  - pose proof (metadata_lower_bound fuel code (p + width i)
      (match i with Entry => p | _ => current end) q own Member) as Bound.
    pose proof (instruction_width_positive i).
    assert (Later : (q <=? p)%nat = false) by (apply Nat.leb_gt; lia).
    rewrite Later. eapply IHfuel; eauto.
Qed.
Lemma metadata_unique fuel code p current : NoDup (map fst (metadata_entries fuel code p current)).
Proof.
  revert p current. induction fuel; intros p current; cbn [metadata_entries map]; [constructor |].
  destruct (decode code p) as [i|]; [|constructor]. cbn [map]. constructor.
  - intro Member. apply in_map_iff in Member. destruct Member as [[q own] [Same Member]].
    cbn [fst] in Same. subst q.
    pose proof (metadata_lower_bound fuel code (p + width i)
      (match i with Entry => p | _ => current end) p own Member).
    pose proof (instruction_width_positive i). lia.
  - apply IHfuel.
Qed.
Fixpoint metadata_lookup q (entries : list (nat * nat)) :=
  match entries with
  | [] => None
  | (p, own) :: entries => if Nat.eqb q p then Some own else metadata_lookup q entries
  end.
Lemma metadata_lookup_some q entries own : metadata_lookup q entries = Some own -> In (q, own) entries.
Proof.
  induction entries as [|[p current] entries IH]; [discriminate |].
  cbn [metadata_lookup]. destruct (q =? p)%nat eqn:Same.
  - apply Nat.eqb_eq in Same. subst p. intro Equal. inversion Equal. now left.
  - intro Found. right. now apply IH.
Qed.
Lemma metadata_lookup_none q entries : metadata_lookup q entries = None <-> ~ In q (map fst entries).
Proof.
  induction entries as [|[p current] entries IH]; [cbn; tauto |].
  cbn [metadata_lookup map fst]. destruct (q =? p)%nat eqn:Same.
  - apply Nat.eqb_eq in Same. subst p. split; [discriminate |]. intro Missing. exfalso. apply Missing. now left.
  - apply Nat.eqb_neq in Same. rewrite IH. cbn [In]. intuition congruence.
Qed.
Lemma metadata_boundary code q :
  boundary code q = match metadata_lookup q (metadata_entries (length code) code 0 0) with Some _ => true | None => false end.
Proof.
  unfold boundary, boundaries. rewrite <- (metadata_positions (length code) code 0 0).
  destruct (metadata_lookup q (metadata_entries (length code) code 0 0)) as [own|] eqn:Lookup.
  - apply existsb_exists. exists q. split; [|apply Nat.eqb_refl].
    apply in_map_iff. exists (q,own). split; [reflexivity |]. now apply metadata_lookup_some.
  - apply metadata_lookup_none in Lookup. destruct (existsb (Nat.eqb q) (map fst (metadata_entries (length code) code 0 0))) eqn:Found; auto.
    apply existsb_exists in Found. destruct Found as [p [Member Same]]. apply Nat.eqb_eq in Same. subst p. contradiction.
Qed.
Lemma metadata_owner_value code q :
  owner_value code q = match metadata_lookup q (metadata_entries (length code) code 0 0) with
    Some own => Vlong (Int64.repr (Z.of_nat own)) | None => Vlong Int64.zero end.
Proof.
  unfold owner_value. rewrite metadata_boundary.
  destruct (metadata_lookup q (metadata_entries (length code) code 0 0)) as [own|] eqn:Lookup; [|reflexivity].
  cbn. unfold owner. rewrite (metadata_owner (length code) code 0 0 q own); [reflexivity |].
  now apply metadata_lookup_some.
Qed.
Lemma metadata_past_end fuel code p current : (length code <= p)%nat -> metadata_entries fuel code p current = [].
Proof.
  intro Beyond. destruct fuel; [reflexivity |]. cbn [metadata_entries].
  assert (Decoded : decode code p = None).
  { unfold decode. rewrite skipn_all2 by exact Beyond. reflexivity. }
  now rewrite Decoded.
Qed.
Lemma metadata_enough fuel code p current : (length code - p <= fuel)%nat -> forall extra,
  (length code - p <= extra)%nat -> metadata_entries fuel code p current = metadata_entries extra code p current.
Proof.
  revert p current. induction fuel; intros p current Space extra Enough.
  - rewrite !metadata_past_end by lia. reflexivity.
  - destruct (decode code p) as [i|] eqn:Decoded.
    + pose proof (decode_bounds code p i Decoded) as Bounds.
      pose proof (decode_position code p i Decoded) as Position.
      pose proof (instruction_width_positive i) as Width.
      destruct extra as [|extra]; [lia |]. cbn [metadata_entries]. rewrite Decoded.
      f_equal. apply IHfuel; lia.
    + destruct extra; cbn [metadata_entries]; now rewrite ?Decoded.
Qed.
Lemma metadata_advance code p current i : decode code p = Some i ->
  metadata_entries (length code - p) code p current =
  (p, match i with Entry => p | _ => current end) ::
  metadata_entries (length code - (p + width i)) code (p + width i)
    (match i with Entry => p | _ => current end).
Proof.
  intro Decoded. pose proof (decode_bounds code p i Decoded) as Bounds.
  pose proof (decode_position code p i Decoded) as Position.
  pose proof (instruction_width_positive i) as Width.
  destruct (length code - p) as [|fuel] eqn:Remaining; [lia |].
  cbn [metadata_entries]. rewrite Decoded. f_equal. apply metadata_enough; lia.
Qed.
Definition metadata_set {A} (prior : nat -> A) p value :=
  fun q => if Nat.eqb q p then value else prior q.
Fixpoint metadata_install {A} entries (value : nat -> A) (prior : nat -> A) :=
  match entries with
  | [] => prior
  | (p, own) :: entries => metadata_install entries value (metadata_set prior p (value own))
  end.
Lemma metadata_install_none {A} entries (value : nat -> A) prior q :
  metadata_lookup q entries = None -> metadata_install entries value prior q = prior q.
Proof.
  revert prior. induction entries as [|[p own] entries IH]; intros prior Missing; [reflexivity |].
  cbn [metadata_lookup] in Missing. destruct (q =? p) eqn:Same; [discriminate |].
  cbn [metadata_install]. rewrite IH by exact Missing. unfold metadata_set. now rewrite Same.
Qed.
Lemma metadata_install_some {A} entries (value : nat -> A) prior q own :
  NoDup (map fst entries) -> metadata_lookup q entries = Some own ->
  metadata_install entries value prior q = value own.
Proof.
  revert prior. induction entries as [|[p current] entries IH]; intros prior Unique Found; [discriminate |].
  inversion Unique as [|p0 positions Missing Tail]; subst.
  cbn [metadata_lookup] in Found. destruct (q =? p) eqn:Same.
  - apply Nat.eqb_eq in Same. subst p. inversion Found; subst current.
    cbn [metadata_install]. rewrite metadata_install_none.
    + unfold metadata_set. now rewrite Nat.eqb_refl.
    + now apply metadata_lookup_none.
  - cbn [metadata_install]. now apply IH.
Qed.
Lemma metadata_installed_owner code q :
  metadata_install (metadata_entries (length code) code 0 0)
    (fun own => Vlong (Int64.repr (Z.of_nat own))) (fun _ => Vlong Int64.zero) q = owner_value code q.
Proof.
  rewrite metadata_owner_value.
  destruct (metadata_lookup q (metadata_entries (length code) code 0 0)) as [own|] eqn:Lookup.
  - exact (metadata_install_some (metadata_entries (length code) code 0 0)
      (fun own => Vlong (Int64.repr (Z.of_nat own))) (fun _ => Vlong Int64.zero) q own
      (metadata_unique (length code) code 0 0) Lookup).
  - exact (metadata_install_none (metadata_entries (length code) code 0 0)
      (fun own => Vlong (Int64.repr (Z.of_nat own))) (fun _ => Vlong Int64.zero) q Lookup).
Qed.
Lemma metadata_installed_boundary code q :
  metadata_install (metadata_entries (length code) code 0 0)
    (fun _ => Vint Int.one) (fun _ => Vint Int.zero) q = boundary_value code q.
Proof.
  unfold boundary_value. rewrite metadata_boundary.
  destruct (metadata_lookup q (metadata_entries (length code) code 0 0)) as [own|] eqn:Lookup.
  - exact (metadata_install_some (metadata_entries (length code) code 0 0)
      (fun _ => Vint Int.one) (fun _ => Vint Int.zero) q own
      (metadata_unique (length code) code 0 0) Lookup).
  - exact (metadata_install_none (metadata_entries (length code) code 0 0)
      (fun _ => Vint Int.one) (fun _ => Vint Int.zero) q Lookup).
Qed.
Lemma metadata_tabulate_set {A} {default : Inhabitant A} size (prior : nat -> A) p value :
  (p < size)%nat ->
  map (metadata_set prior p value) (seq 0 size) =
  upd_Znth (Z.of_nat p) (map prior (seq 0 size)) value.
Proof.
  intro Position. apply Znth_eq_ext.
  - rewrite Zlength_upd_Znth, !Zlength_map, !Zlength_correct, !length_seq. reflexivity.
  - intros index Range. rewrite Zlength_map, Zlength_correct, length_seq in Range.
    rewrite <- (Z2Nat.id index) by lia.
    rewrite tabulated_lookup by lia. rewrite Nat2Z.id. unfold metadata_set.
    destruct (Nat.eq_dec (Z.to_nat index) p) as [Same | Different].
    + subst p. rewrite Nat.eqb_refl, upd_Znth_same by
        (rewrite Zlength_map, Zlength_correct, length_seq; lia). reflexivity.
    + assert (Other : (Z.to_nat index =? p) = false) by (apply Nat.eqb_neq; exact Different).
      rewrite Other, upd_Znth_diff by
        (rewrite ?Zlength_map, ?Zlength_correct, ?length_seq; lia).
      rewrite tabulated_lookup by lia. now rewrite Nat2Z.id.
Qed.

Section Allocation.
Local Open Scope Z_scope.
Local Open Scope logic.
Context (allocation_token : type -> val -> mpred).
Definition allocation_block t p :=
  if eq_dec p nullval then emp else allocation_token t p * data_at_ Tsh t p.
Lemma allocation_block_pointer t p : allocation_block t p |-- !! (is_pointer_or_null p).
Proof.
  unfold allocation_block. destruct (eq_dec p nullval); subst; entailer!.
Qed.
#[local] Hint Resolve allocation_block_pointer : saturate_local.
Definition free_metadata_spec : ident * funspec :=
 DECLARE _free
 WITH t : type, p : val
 PRE [tptr tvoid] PROP () PARAMS (p) SEP (allocation_block t p)
 POST [tvoid] PROP () RETURN () SEP ().
Definition destroy_spec : ident * funspec :=
 DECLARE _icevm_code_destroy
 WITH ctx : val, flags : val, owners : val, flag_type : type, owner_type : type
 PRE [tptr (Tstruct _icevm_code noattr)]
   PROP () PARAMS (ctx)
   SEP (field_at Tsh (Tstruct _icevm_code noattr) [StructField _boundary] flags ctx;
     field_at Tsh (Tstruct _icevm_code noattr) [StructField _owner] owners ctx;
     allocation_block flag_type flags; allocation_block owner_type owners)
 POST [tvoid] PROP () RETURN ()
   SEP (field_at Tsh (Tstruct _icevm_code noattr) [StructField _boundary] nullval ctx;
     field_at Tsh (Tstruct _icevm_code noattr) [StructField _owner] nullval ctx).
Definition allocation_Gprog := [free_metadata_spec; destroy_spec] ++ Gprog.
Lemma body_destroy : semax_body Vprog allocation_Gprog f_icevm_code_destroy destroy_spec.
Proof.
  start_function.
  assert_PROP (is_pointer_or_null flags) as FlagsPointer by entailer!.
  assert_PROP (is_pointer_or_null owners) as OwnersPointer by entailer!.
  forward. forward_call (flag_type, flags).
  forward. forward_call (owner_type, owners). forward. forward. entailer!.
Qed.
End Allocation.
