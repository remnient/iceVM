From Stdlib Require Import List NArith Arith Bool Lia.
From IceVM Require Import Syntax State.
Import ListNotations.
Fixpoint scan (fuel : nat) (code : list nat) (p : nat) : list nat :=
  match fuel with
  | 0 => []
  | S fuel => match decode code p with
              | Some i => p :: scan fuel code (p + width i)
              | None => [] end
  end.
Definition boundaries code := scan (length code) code 0.
Definition boundary code p := existsb (Nat.eqb p) (boundaries code).
Fixpoint owner_at (fuel : nat) (code : list nat) (p current target : nat) : nat :=
  match fuel with
  | 0 => current
  | S fuel =>
      match decode code p with
      | None => current
      | Some i =>
          let own := match i with Entry => p | _ => current end in
          if target <=? p then own else owner_at fuel code (p + width i) own target
      end
  end.
Definition owner code p := owner_at (length code) code 0 0 p.
Definition local_target code from target :=
  boundary code from && boundary code target && Nat.eqb (owner code from) (owner code target).
Definition call_target code target :=
  boundary code target &&
  match decode code target with Some Entry => negb (Nat.eqb target 0) && negb (Nat.eqb (owner code target) 0) | _ => false end.
Definition transfer code s t :=
  if local_target code (pc s) t then at_pc s t else finish s (Fault Target).
Definition execute (code : list nat) (s : state) (i : instr) : state :=
  let next := at_pc s (pc s + width i) in
  match i with
  | Halt => finish s Stopped
  | Trap => finish s (Fault Explicit)
  | Entry | Nop | Pad _ => next
  | Imm d x => write_reg next d x
  | Move d a => write_reg next d (regs s a)
  | Binary op d a b =>
      match eval_bin op (regs s a) (regs s b) with
      | Some v => write_reg next d v | None => finish s (Fault Division) end
  | Load d a =>
      let addr := N.to_nat (regs s a) in
      if addr + 8 <=? frontier s then write_reg next d (read64 (mem s) addr)
      else finish s (Fault Memory)
  | Store a b =>
      let addr := N.to_nat (regs s a) in
      if addr + 8 <=? frontier s then
        State (pc next) (regs s) (write64 (mem s) addr (regs s b)) (frontier s) (frames s) Running
      else finish s (Fault Memory)
  | Alloc d a =>
      let n := N.to_nat (regs s a) in
      if frontier s + n <=? memory_size then
        write_reg (State (pc next) (regs s) (clear (mem s) (frontier s) (frontier s + n))
                         (frontier s + n) (frames s) Running) d (N.of_nat (frontier s))
      else finish s (Fault Memory)
  | Mark d => write_reg next d (N.of_nat (frontier s))
  | Reset a =>
      let n := N.to_nat (regs s a) in
      if n <=? frontier s then
        State (pc next) (regs s) (mem s) n (frames s) Running
      else finish s (Fault Region)
  | Jump t => transfer code s t
  | Branch a t => if N.eqb (regs s a) 0 then next else transfer code s t
  | Indirect a => transfer code s (N.to_nat (regs s a))
  | Call t =>
      if call_target code t && local_target code (pc s) (pc next) then
        if length (frames s) <? stack_size then
          State t (regs s) (mem s) (frontier s) (Frame (pc next) (regs s) :: frames s) Running
        else finish s (Fault Stack)
      else finish s (Fault Target)
  | Ret =>
      match frames s with
      | [] => finish s (Fault Stack)
      | f :: fs =>
          if boundary code (return_pc f) then
            State (return_pc f) (put (saved f) 0 (regs s 0)) (mem s) (frontier s) fs Running
          else finish s (Fault Target)
      end
  end.
Inductive transition (code : list nat) : state -> state -> Prop :=
| decoded s i : mode s = Running -> decode code (pc s) = Some i ->
    transition code s (execute code s i)
| malformed s : mode s = Running -> decode code (pc s) = None ->
    transition code s (finish s (Fault Decode)).
Theorem transition_deterministic code s a b :
  transition code s a -> transition code s b -> a = b.
Proof.
  intros Ha Hb. inversion Ha; inversion Hb; subst; try congruence.
Qed.
Local Opaque memory_size stack_size.
Lemma execute_well_formed code s i : well_formed s -> well_formed (execute code s i).
Proof.
  intros [Hmem Hstack]. destruct i; cbn [execute];
  unfold transfer, write_reg, at_pc, finish; cbn;
  repeat match goal with
  | |- context [if ?b then _ else _] => destruct b eqn:?
  | |- context [match ?x with Some _ => _ | None => _ end] => destruct x eqn:?
  | |- context [match frames s with _ => _ end] => destruct (frames s) eqn:?
  end;
  unfold well_formed; cbn -[Nat.ltb] in *;
  repeat match goal with
  | H : (_ <=? _) = true |- _ => apply Nat.leb_le in H
  | H : (_ <? _) = true |- _ => apply Nat.ltb_lt in H
  end; split; try assumption; try lia.
  change ((length (frames s) <? stack_size) = true) in Heqb0.
  apply Nat.ltb_lt in Heqb0. lia.
Qed.
Theorem transition_well_formed code s t :
  well_formed s -> transition code s t -> well_formed t.
Proof.
  intros H T. inversion T; subst.
  - now apply execute_well_formed.
  - exact H.
Qed.
Lemma execute_canonical code s i : canonical s -> canonical (execute code s i).
Proof.
  intros [Hr [Hm Hf]]. destruct i; cbn [execute];
  unfold transfer, write_reg, at_pc, finish; cbn;
  repeat match goal with
  | |- context [if ?b then _ else _] => destruct b eqn:?
  | |- context [match ?x with Some _ => _ | None => _ end] => destruct x eqn:?
  | |- context [match frames s with _ => _ end] => destruct (frames s) eqn:?
  end;
  unfold canonical; cbn;
  repeat split; auto using put_canonical, write64_canonical, clear_canonical;
  inversion Hf; subst; auto using put_canonical.
Qed.
Theorem transition_canonical code s t : canonical s -> transition code s t -> canonical t.
Proof. intros H T. inversion T; subst; eauto using execute_canonical. Qed.
