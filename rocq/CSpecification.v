From VST.floyd Require Import proofauto.
From IceVMC Require Import CProgram.
From IceVM Require Import Syntax CRepresentation CIntegers Semantics.
Import ListNotations.
Definition trap_spec : ident * funspec :=
 DECLARE _trap
 WITH s : val, f : Z, old_status : Z, old_fault : Z
 PRE [ tptr (Tstruct _icevm noattr), tint ]
   PROP (0 <= f <= 6)
   PARAMS (s; Vint (Int.repr f))
   SEP (field_at Tsh (Tstruct _icevm noattr) [StructField _status] (Vint (Int.repr old_status)) s;
        field_at Tsh (Tstruct _icevm noattr) [StructField _fault] (Vint (Int.repr old_fault)) s)
 POST [ tvoid ] PROP () RETURN ()
   SEP (field_at Tsh (Tstruct _icevm noattr) [StructField _status] (Vint (Int.repr 2)) s;
        field_at Tsh (Tstruct _icevm noattr) [StructField _fault] (Vint (Int.repr f)) s).
Fixpoint byte_sum (contents : list Z) (count : nat) : Z :=
  match count with
  | O => 0
  | S n => byte_sum contents n + Znth (Z.of_nat n) contents * 2 ^ (8 * Z.of_nat n)
  end.
Lemma byte_sum_correspondence bytes n : byte_sum bytes n = z_byte_sum bytes n.
Proof.
  induction n; cbn [byte_sum z_byte_sum]; [reflexivity |].
  rewrite IHn. unfold Znth. rewrite if_false by lia. now rewrite Nat2Z.id.
Qed.
Lemma byte_sum_complete bytes : byte_sum bytes (length bytes) = z_little bytes.
Proof. rewrite byte_sum_correspondence. apply z_byte_sum_complete. Qed.
Definition read64_spec : ident * funspec :=
 DECLARE _read64
 WITH p : val, sh : share, contents : list Z
 PRE [ tptr tuchar ]
   PROP (readable_share sh; Zlength contents = 8; Forall (fun b => 0 <= b <= 255) contents)
   PARAMS (p)
   SEP (data_at sh (tarray tuchar 8) (map (fun b => Vint (Int.repr b)) contents) p)
 POST [ tulong ] PROP () RETURN (Vlong (Int64.repr (byte_sum contents 8)))
   SEP (data_at sh (tarray tuchar 8) (map (fun b => Vint (Int.repr b)) contents) p).
Definition boundary_spec : ident * funspec :=
 DECLARE _boundary
 WITH sh : share, c : val, flags : val, code : list nat, p : nat
 PRE [ tptr (Tstruct _icevm_code noattr), tulong ]
   PROP (readable_share sh; Z.of_nat (length code) <= 4294967295;
         Z.of_nat p <= Int64.max_unsigned)
   PARAMS (c; Vlong (Int64.repr (Z.of_nat p)))
   SEP (field_at sh (Tstruct _icevm_code noattr) [StructField _size]
          (Vlong (Int64.repr (Z.of_nat (length code)))) c;
        field_at sh (Tstruct _icevm_code noattr) [StructField _boundary] flags c;
        data_at sh (tarray tuchar (Z.of_nat (length code))) (boundary_values code) flags)
 POST [ tint ] PROP () RETURN (boundary_value code p)
   SEP (field_at sh (Tstruct _icevm_code noattr) [StructField _size]
          (Vlong (Int64.repr (Z.of_nat (length code)))) c;
        field_at sh (Tstruct _icevm_code noattr) [StructField _boundary] flags c;
        data_at sh (tarray tuchar (Z.of_nat (length code))) (boundary_values code) flags).
Definition local_boundaries code p t := (Semantics.boundary code p && Semantics.boundary code t)%bool.
Definition local_spec : ident * funspec :=
 DECLARE _local
 WITH sh : share, c : val, bytes : val, flags : val, owners : val, code : list nat, p : nat, t : nat
 PRE [ tptr (Tstruct _icevm_code noattr), tulong, tulong ]
   PROP (Z.of_nat p <= Int64.max_unsigned; Z.of_nat t <= Int64.max_unsigned)
   PARAMS (c; Vlong (Int64.repr (Z.of_nat p)); Vlong (Int64.repr (Z.of_nat t)))
   SEP (represents_code sh c bytes flags owners code)
 POST [ tint ] PROP () RETURN (Vint (Int.repr (if local_target code p t then 1 else 0)))
   SEP (represents_code sh c bytes flags owners code).
Definition call_boundary code t := (negb (Nat.eqb t 0) && Semantics.boundary code t)%bool.
Definition call_entry code t := (call_boundary code t && Nat.eqb (nth t code 0%nat) 2)%bool.
Definition callable_spec : ident * funspec :=
 DECLARE _callable
 WITH sh : share, c : val, bytes : val, flags : val, owners : val, code : list nat, t : nat
 PRE [ tptr (Tstruct _icevm_code noattr), tulong ]
   PROP (Z.of_nat t <= Int64.max_unsigned)
   PARAMS (c; Vlong (Int64.repr (Z.of_nat t)))
   SEP (represents_code sh c bytes flags owners code)
 POST [ tint ] PROP () RETURN (Vint (Int.repr (if call_target code t then 1 else 0)))
   SEP (represents_code sh c bytes flags owners code).
Lemma call_guard_result code t : call_target code t =
  (call_entry code t && negb (Nat.eqb (owner code t) 0))%bool.
Proof.
  rewrite call_target_header. unfold call_entry, call_boundary.
  destruct (Semantics.boundary code t), (Nat.eqb t 0), (Nat.eqb (nth t code 0%nat) 2),
    (Nat.eqb (owner code t) 0); reflexivity.
Qed.
Definition decode_result output result : mpred :=
  match result with
  | Some i => data_at Tsh (Tstruct _icevm_instruction noattr) (instruction_value i) output
  | None => data_at_ Tsh (Tstruct _icevm_instruction noattr) output end.
Definition decoder_spec : ident * funspec :=
 DECLARE _icevm_decode
 WITH sh : share, c : val, bytes : val, output : val, code : list nat, p : nat
 PRE [ tptr (Tstruct _icevm_code noattr), tulong, tptr (Tstruct _icevm_instruction noattr) ]
   PROP (readable_share sh; Forall (fun b => (b < 256)%nat) code;
         Z.of_nat (length code) <= 4294967295; Z.of_nat p <= Int64.max_unsigned)
   PARAMS (c; Vlong (Int64.repr (Z.of_nat p)); output)
   SEP (field_at sh (Tstruct _icevm_code noattr) [StructField _size]
          (Vlong (Int64.repr (Z.of_nat (length code)))) c;
        field_at sh (Tstruct _icevm_code noattr) [StructField _bytes] bytes c;
        data_at sh (tarray tuchar (Z.of_nat (length code))) (code_values code) bytes;
        data_at_ Tsh (Tstruct _icevm_instruction noattr) output)
 POST [ tint ] PROP () RETURN (Vint (Int.repr (match decode code p with Some _ => 1 | None => 0 end)))
   SEP (field_at sh (Tstruct _icevm_code noattr) [StructField _size]
          (Vlong (Int64.repr (Z.of_nat (length code)))) c;
        field_at sh (Tstruct _icevm_code noattr) [StructField _bytes] bytes c;
        data_at sh (tarray tuchar (Z.of_nat (length code))) (code_values code) bytes;
        decode_result output (decode code p)).
Definition Gprog : funspecs := ltac:(with_library prog
  [trap_spec; read64_spec; boundary_spec; local_spec; callable_spec; decoder_spec]).
