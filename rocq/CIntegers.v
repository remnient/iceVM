From Stdlib Require Import List NArith ZArith Lia.
From compcert.lib Require Import Integers.
From IceVM Require Import Syntax State.
Import ListNotations.
Definition cword (n : N) := Int64.repr (Z.of_N n).
Lemma cword_word n : cword (word n) = cword n.
Proof.
  unfold cword, word. rewrite N2Z.inj_mod.
  change (Int64.repr (Z.of_N n mod Int64.modulus) = Int64.repr (Z.of_N n)).
  rewrite <- Int64.unsigned_repr_eq. apply Int64.repr_unsigned.
Qed.
Lemma cword_unsigned n : (n < modulus)%N -> Int64.unsigned (cword n) = Z.of_N n.
Proof.
  intro Bound. unfold cword. apply Int64.unsigned_repr.
  change (0 <= Z.of_N n <= 18446744073709551615)%Z. unfold modulus in Bound. lia.
Qed.
Definition cbinop op x y :=
  match op with
  | Add => Some (Int64.add x y) | Sub => Some (Int64.sub x y) | Mul => Some (Int64.mul x y)
  | Div => if Int64.eq y Int64.zero then None else Some (Int64.divu x y)
  | And => Some (Int64.and x y) | Or => Some (Int64.or x y) | Xor => Some (Int64.xor x y)
  | Shl => Some (Int64.shl x (Int64.and y (Int64.repr 63)))
  | Shr => Some (Int64.shru x (Int64.and y (Int64.repr 63)))
  | Eq => Some (Int64.repr (if Int64.eq x y then 1 else 0))
  | Lt => Some (Int64.repr (if Int64.ltu x y then 1 else 0))
  end.
Lemma cword_eq x y : (x < modulus)%N -> (y < modulus)%N ->
  Int64.eq (cword x) (cword y) = N.eqb x y.
Proof.
  intros X Y. unfold Int64.eq. rewrite !cword_unsigned by assumption.
  destruct (Coqlib.zeq (Z.of_N x) (Z.of_N y)); destruct (N.eqb x y) eqn:E; auto;
    apply N.eqb_eq in E || apply N.eqb_neq in E; exfalso; lia.
Qed.
Lemma cword_ltu x y : (x < modulus)%N -> (y < modulus)%N ->
  Int64.ltu (cword x) (cword y) = N.ltb x y.
Proof.
  intros X Y. unfold Int64.ltu. rewrite !cword_unsigned by assumption.
  destruct (Coqlib.zlt (Z.of_N x) (Z.of_N y)); destruct (N.ltb x y) eqn:E; auto;
    apply N.ltb_lt in E || apply N.ltb_ge in E; exfalso; lia.
Qed.
Lemma cword_mask y : (y < modulus)%N ->
  Int64.and (cword y) (Int64.repr 63) = cword (N.land y 63).
Proof.
  intro Y. unfold Int64.and, cword. rewrite (Int64.unsigned_repr 63) by (change (0 <= 63 <= 18446744073709551615)%Z; lia).
  fold (cword y). rewrite cword_unsigned by exact Y. rewrite N2Z.inj_land. reflexivity.
Qed.
Theorem cbinop_correspondence op x y : (x < modulus)%N -> (y < modulus)%N ->
  option_map cword (eval_bin op x y) = cbinop op (cword x) (cword y).
Proof.
  intros X Y. destruct op; cbn [eval_bin cbinop option_map].
  - rewrite cword_word. unfold Int64.add. rewrite !cword_unsigned by assumption.
    unfold cword. now rewrite N2Z.inj_add.
  - rewrite cword_word. unfold Int64.sub. rewrite !cword_unsigned by assumption.
    unfold cword. rewrite N2Z.inj_sub by (unfold modulus in *; lia). rewrite N2Z.inj_add.
    f_equal. apply Int64.eqm_samerepr. unfold Int64.eqm, Zbits.eqmod.
    exists 1%Z. change (Z.of_N x + 18446744073709551616 - Z.of_N y =
      1 * 18446744073709551616 + (Z.of_N x - Z.of_N y))%Z. lia.
  - rewrite cword_word. unfold Int64.mul. rewrite !cword_unsigned by assumption.
    unfold cword. now rewrite N2Z.inj_mul.
  - change (option_map cword (if N.eqb y 0 then None else Some (N.div x y)) =
      (if Int64.eq (cword y) (cword 0) then None else Some (Int64.divu (cword x) (cword y)))).
    rewrite cword_eq by (try assumption; reflexivity). destruct (N.eqb y 0); cbn; auto.
    unfold Int64.divu. rewrite !cword_unsigned by assumption. unfold cword. now rewrite N2Z.inj_div.
  - unfold Int64.and. rewrite !cword_unsigned by assumption. unfold cword. now rewrite N2Z.inj_land.
  - rewrite cword_word. unfold Int64.or. rewrite !cword_unsigned by assumption. unfold cword. now rewrite N2Z.inj_lor.
  - rewrite cword_word. unfold Int64.xor. rewrite !cword_unsigned by assumption. unfold cword. now rewrite N2Z.inj_lxor.
  - rewrite cword_word, cword_mask by exact Y. unfold Int64.shl.
    rewrite !cword_unsigned by (try assumption; pose proof (N.land_le_r y 63); unfold modulus; lia).
    unfold cword. now rewrite N2Z.inj_shiftl.
  - rewrite cword_mask by exact Y. unfold Int64.shru.
    rewrite !cword_unsigned by (try assumption; pose proof (N.land_le_r y 63); unfold modulus; lia).
    unfold cword. now rewrite N2Z.inj_shiftr.
  - rewrite cword_eq by assumption. destruct (N.eqb x y); reflexivity.
  - rewrite cword_ltu by assumption. destruct (N.ltb x y); reflexivity.
Qed.
Lemma c_add_repr x y : Int64.add (Int64.repr x) (Int64.repr y) = Int64.repr (x + y).
Proof.
  unfold Int64.add. apply Int64.eqm_samerepr. apply Int64.eqm_add;
    apply Int64.eqm_sym; apply Int64.eqm_unsigned_repr.
Qed.
Lemma c_mul_repr x y : Int64.mul (Int64.repr x) (Int64.repr y) = Int64.repr (x * y).
Proof.
  unfold Int64.mul. apply Int64.eqm_samerepr. apply Int64.eqm_mult;
    apply Int64.eqm_sym; apply Int64.eqm_unsigned_repr.
Qed.
Lemma c_byte_shift x k : (0 <= x <= 255)%Z -> (0 <= k < 64)%Z ->
  Int64.shl' (Int64.repr x) (Int.repr k) = Int64.repr (x * 2 ^ k).
Proof.
  intros X K. unfold Int64.shl'.
  rewrite Int64.unsigned_repr by (change (0 <= x <= 18446744073709551615)%Z; lia).
  rewrite Int.unsigned_repr by (change (0 <= k <= 4294967295)%Z; lia).
  rewrite Z.shiftl_mul_pow2 by lia. reflexivity.
Qed.
Fixpoint z_little (bytes : list Z) : Z :=
  match bytes with nil => 0 | b :: bytes => b + 256 * z_little bytes end.
Fixpoint z_byte_sum (bytes : list Z) count : Z :=
  match count with
  | O => 0
  | S n => z_byte_sum bytes n + List.nth n bytes 0%Z * 2 ^ (8 * Z.of_nat n)
  end.
Lemma z_byte_sum_cons b bytes count :
  z_byte_sum (b :: bytes) (S count) = (b + 256 * z_byte_sum bytes count)%Z.
Proof.
  induction count.
  - change (0 + b * 1 = b + 256 * 0)%Z. ring.
  - change (z_byte_sum (b :: bytes) (S count) + List.nth count bytes 0%Z * 2 ^ (8 * Z.of_nat (S count)) =
      b + 256 * (z_byte_sum bytes count + List.nth count bytes 0%Z * 2 ^ (8 * Z.of_nat count)))%Z.
    rewrite IHcount.
  replace (8 * Z.of_nat (S count))%Z with (8 + 8 * Z.of_nat count)%Z by lia.
  rewrite Z.pow_add_r by lia. change (2 ^ 8)%Z with 256%Z. ring.
Qed.
Lemma z_byte_sum_complete bytes : z_byte_sum bytes (List.length bytes) = z_little bytes.
Proof. induction bytes; cbn [List.length z_little]; [reflexivity |]. now rewrite z_byte_sum_cons, IHbytes. Qed.
Lemma z_little_correspondence bytes : List.Forall (fun b => (0 <= b)%Z) bytes ->
  Z.of_N (little (List.map Z.to_nat bytes)) = z_little bytes.
Proof.
  intro B. induction B; cbn [List.map little z_little]; [reflexivity |].
  rewrite N2Z.inj_add, N2Z.inj_mul, nat_N_Z, Z2Nat.id by assumption.
  now rewrite IHB.
Qed.
Lemma c_int_mul_repr x y : Int.mul (Int.repr x) (Int.repr y) = Int.repr (x * y).
Proof.
  unfold Int.mul. apply Int.eqm_samerepr. apply Int.eqm_mult;
    apply Int.eqm_sym; apply Int.eqm_unsigned_repr.
Qed.
Lemma c_access_interval h x :
  ((Z.of_N x <= Z.of_nat h) /\ (8 <= Z.of_nat h - Z.of_N x))%Z <-> (N.to_nat x + 8 <= h)%nat.
Proof. pose proof (N_nat_Z x). lia. Qed.
Lemma c_allocation_interval h x :
  (Z.of_N x <= Z.of_nat memory_size - Z.of_nat h)%Z <-> (h + N.to_nat x <= memory_size)%nat.
Proof. pose proof (N_nat_Z x). lia. Qed.
