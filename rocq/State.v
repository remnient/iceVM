From Stdlib Require Import List NArith Arith Bool Lia.
From IceVM Require Import Syntax.
Import ListNotations.
Definition memory_size := 65536.
Definition stack_size := 256.
Definition registers := nat -> N.
Definition memory := nat -> N.
Definition put (r : registers) (d : nat) (v : N) : registers :=
  fun n => if Nat.eqb n d then word v else r n.
Inductive fault := Explicit | Decode | Target | Memory | Region | Stack | Division.
Inductive status := Running | Stopped | Fault (why : fault).
Record frame := Frame { return_pc : nat; saved : registers }.
Record state := State {
  pc : nat; regs : registers; mem : memory; frontier : nat;
  frames : list frame; mode : status
}.
Definition initial : state := State 0 (fun _ => 0%N) (fun _ => 0%N) 0 [] Running.
Definition at_pc (s : state) (p : nat) := State p (regs s) (mem s) (frontier s) (frames s) Running.
Definition finish (s : state) (m : status) :=
  State (pc s) (regs s) (mem s) (frontier s) (frames s) m.
Definition write_reg (s : state) (d : nat) (v : N) :=
  State (pc s) (put (regs s) d v) (mem s) (frontier s) (frames s) (mode s).
Definition read64 (m : memory) (a : nat) : N :=
  little (map (fun i => N.to_nat (m (a + i))) (seq 0 8)).
Definition write64 (m : memory) (a : nat) (v : N) : memory :=
  fun i => if (a <=? i) && (i <? a + 8)
           then N.land (N.shiftr v (N.of_nat (8 * (i - a)))) 255 else m i.
Definition clear (m : memory) (lo hi : nat) : memory :=
  fun i => if (lo <=? i) && (i <? hi) then 0%N else m i.
Definition well_formed (s : state) : Prop :=
  frontier s <= memory_size /\ length (frames s) <= stack_size.
Lemma initial_well_formed : well_formed initial.
Proof. split; apply Nat.le_0_l. Qed.
Lemma word_bounded x : (word x < modulus)%N.
Proof. apply N.mod_lt. discriminate. Qed.
Lemma put_same r d x : put r d x d = word x.
Proof. unfold put. now rewrite Nat.eqb_refl. Qed.
Lemma put_other r d x n : n <> d -> put r d x n = r n.
Proof. intro H. unfold put. apply Nat.eqb_neq in H. now rewrite H. Qed.
Definition canonical_registers (r : registers) := forall n, (r n < modulus)%N.
Definition canonical_memory (m : memory) := forall n, (m n < 256)%N.
Definition canonical s := canonical_registers (regs s) /\ canonical_memory (mem s) /\
                          Forall (fun f => canonical_registers (saved f)) (frames s).
Lemma put_canonical r d v : canonical_registers r -> canonical_registers (put r d v).
Proof. intros H n. unfold put. destruct (Nat.eqb n d); auto using word_bounded. Qed.
Lemma write64_canonical m a v : canonical_memory m -> canonical_memory (write64 m a v).
Proof.
  intros H n. unfold write64. destruct ((a <=? n) && (n <? a + 8)); auto.
  pose proof (N.land_le_r (N.shiftr v (N.of_nat (8 * (n - a)))) 255). lia.
Qed.
Lemma clear_canonical m lo hi : canonical_memory m -> canonical_memory (clear m lo hi).
Proof. intros H n. unfold clear. destruct ((lo <=? n) && (n <? hi)); auto. reflexivity. Qed.
Lemma initial_canonical : canonical initial.
Proof. split; [intro n; reflexivity | split; [intro n; reflexivity | constructor]]. Qed.
