From Stdlib Require Import List NArith Arith Bool Lia.
From Loosevm Require Import Syntax Compiler.
Import ListNotations.
Fixpoint byte_power count : N := match count with 0 => 1 | S n => (256 * byte_power n)%N end.
Fixpoint encode_immediate (count : nat) (n : N) : list nat :=
  match count with
  | 0 => []
  | S count => N.to_nat (n mod 256)%N :: encode_immediate count (n / 256)%N
  end.
Lemma immediate_length count n : length (encode_immediate count n) = count.
Proof. revert n. induction count; cbn; auto. Qed.
Lemma immediate_little count n : little (encode_immediate count n) = (n mod byte_power count)%N.
Proof.
  revert n. induction count; intro n; cbn [encode_immediate little byte_power].
  - now rewrite N.mod_1_r.
  - rewrite N2Nat.id, IHcount. symmetry. apply N.Div0.mod_mul_r.
Qed.
Lemma immediate_word n : little (encode_immediate 8 n) = word n.
Proof. exact (immediate_little 8 n). Qed.
Definition encode_binop op :=
  match op with Add => 16 | Sub => 17 | Mul => 18 | Div => 19 | And => 20 | Or => 21
  | Xor => 22 | Shl => 23 | Shr => 24 | Eq => 25 | Lt => 26 end.
Definition encode_instruction i :=
  match i with
  | Halt => [0] | Trap => [1] | Entry => [2] | Ret => [3] | Nop => [15]
  | Pad n => [27;n] ++ repeat 0 n
  | Imm d n => [4;d] ++ encode_immediate 8 n
  | Move d a => [5;d;a] | Load d a => [6;d;a] | Store a b => [7;a;b] | Alloc d a => [8;d;a]
  | Mark d => [9;d] | Reset a => [10;a] | Indirect a => [13;a]
  | Jump t => [11] ++ encode_immediate 8 (N.of_nat t)
  | Branch a t => [12;a] ++ encode_immediate 8 (N.of_nat t)
  | Call t => [14] ++ encode_immediate 8 (N.of_nat t)
  | Binary op d a b => [encode_binop op;d;a;b] end.
Definition encodable i :=
  match i with
  | Pad n => n <=? 8
  | Imm d n => reg d && N.eqb (word n) n
  | Move d a | Load d a | Store d a | Alloc d a => reg d && reg a
  | Mark d | Reset d | Indirect d => reg d
  | Jump t | Call t => N.ltb (N.of_nat t) modulus
  | Branch a t => reg a && N.ltb (N.of_nat t) modulus
  | Binary _ d a b => reg d && reg a && reg b
  | _ => true end.
Lemma instruction_length i : length (encode_instruction i) = width i.
Proof.
  destruct i; cbn [encode_instruction width]; rewrite ?length_app, ?immediate_length, ?repeat_length; reflexivity.
Qed.
Local Ltac byte_cons := constructor; [lia |].
Lemma encoded_instruction_bytes i : encodable i = true -> Forall (fun b => b < 256) (encode_instruction i).
Proof.
  assert (Bytes : forall count n, Forall (fun b => b < 256) (encode_immediate count n)).
  { intro count. induction count; intro n; cbn [encode_immediate]; constructor; auto.
    pose proof (N.mod_lt n 256 ltac:(discriminate)). lia. }
  destruct i; cbn [encodable encode_instruction]; intro H;
    repeat match goal with H : (_ && _) = true |- _ => apply andb_true_iff in H; destruct H end;
    repeat match goal with H : reg _ = true |- _ => unfold reg in H; apply Nat.ltb_lt in H end.
  - byte_cons. constructor.
  - byte_cons. constructor.
  - byte_cons. constructor.
  - byte_cons. constructor.
  - byte_cons. constructor.
  - apply Nat.leb_le in H. byte_cons. byte_cons. clear H.
    induction extra; [constructor |]. constructor; [lia | exact IHextra].
  - byte_cons. byte_cons. apply Bytes.
  - do 3 byte_cons. constructor.
  - destruct op; cbn [encode_binop]; do 4 byte_cons; constructor.
  - do 3 byte_cons. constructor.
  - do 3 byte_cons. constructor.
  - do 3 byte_cons. constructor.
  - do 2 byte_cons. constructor.
  - do 2 byte_cons. constructor.
  - byte_cons. apply Bytes.
  - do 2 byte_cons. apply Bytes.
  - do 2 byte_cons. constructor.
  - byte_cons. apply Bytes.
Qed.
Theorem decode_encoding i tail : encodable i = true -> decode (encode_instruction i ++ tail) 0 = Some i.
Proof.
  destruct i; cbn [encodable]; intro H; try reflexivity.
  - apply Nat.leb_le in H. cbn [encode_instruction decode skipn app].
    assert (B : (extra <=? 8) && (extra <=? length (repeat 0 extra ++ tail)) = true).
    { apply andb_true_iff. rewrite length_app, repeat_length. split; apply Nat.leb_le; lia. }
    now rewrite B.
  - apply andb_true_iff in H. destruct H as [D W].
    change ((if reg d then Some (Imm d (little (encode_immediate 8 x))) else None) = Some (Imm d x)).
    rewrite D, immediate_word. apply N.eqb_eq in W. now rewrite W.
  - cbn [encode_instruction decode skipn app]. now rewrite H.
  - destruct op; cbn [encode_instruction encode_binop decode skipn app op_decode]; now rewrite H.
  - cbn [encode_instruction decode skipn app]. now rewrite H.
  - cbn [encode_instruction decode skipn app]. now rewrite H.
  - cbn [encode_instruction decode skipn app]. now rewrite H.
  - cbn [encode_instruction decode skipn app]. now rewrite H.
  - cbn [encode_instruction decode skipn app]. now rewrite H.
  - apply N.ltb_lt in H.
    change (Some (Jump (N.to_nat (little (encode_immediate 8 (N.of_nat target))))) = Some (Jump target)).
    rewrite immediate_word. unfold word. rewrite N.mod_small by exact H. now rewrite Nat2N.id.
  - apply andb_true_iff in H. destruct H as [A B]. apply N.ltb_lt in B.
    change ((if reg a then Some (Branch a (N.to_nat (little (encode_immediate 8 (N.of_nat target))))) else None) = Some (Branch a target)).
    rewrite A, immediate_word. unfold word. rewrite N.mod_small by exact B. now rewrite Nat2N.id.
  - cbn [encode_instruction decode skipn app]. now rewrite H.
  - apply N.ltb_lt in H.
    change (Some (Call (N.to_nat (little (encode_immediate 8 (N.of_nat target))))) = Some (Call target)).
    rewrite immediate_word. unfold word. rewrite N.mod_small by exact H. now rewrite Nat2N.id.
Qed.
Definition encode_program xs := flat_map encode_instruction xs.
Lemma program_length xs : length (encode_program xs) = code_size xs.
Proof. unfold encode_program. induction xs; cbn [flat_map code_size]; auto. rewrite length_app, instruction_length, IHxs. reflexivity. Qed.
Lemma decode_prefix prefix code p : decode (prefix ++ code) (length prefix + p) = decode code p.
Proof. unfold decode. rewrite skipn_app, skipn_all2 by lia. cbn. replace (length prefix + p - length prefix) with p by lia. reflexivity. Qed.
Lemma layout_prefix prefix code p xs : expression_layout code p xs ->
  expression_layout (prefix ++ code) (length prefix + p) xs.
Proof.
  revert p. induction xs; intros p H; cbn [expression_layout] in *; auto.
  destruct H as [D Rest]. split; [now rewrite decode_prefix |].
  replace (length prefix + p + width a) with (length prefix + (p + width a)) by lia. now apply IHxs.
Qed.
Theorem encoded_program_layout xs suffix : Forall (fun i => encodable i = true) xs ->
  expression_layout (encode_program xs ++ suffix) 0 xs.
Proof.
  intro H. induction H; cbn [encode_program flat_map expression_layout]; auto. split.
  - rewrite <- app_assoc. now apply decode_encoding.
  - rewrite <- app_assoc.
    replace (0 + width x) with (length (encode_instruction x) + 0) by (rewrite instruction_length; lia).
    now apply layout_prefix.
Qed.
Lemma encoded_program_bytes xs : Forall (fun i => encodable i = true) xs ->
  Forall (fun b => b < 256) (encode_program xs).
Proof.
  intro H. induction H; cbn [encode_program flat_map]; [constructor |].
  apply Forall_app. split; auto. now apply encoded_instruction_bytes.
Qed.
Definition encode_checked xs :=
  if forallb encodable xs then Some (encode_program xs) else None.
Theorem encode_checked_sound xs code : encode_checked xs = Some code ->
  Forall (fun b => b < 256) code /\ expression_layout code 0 xs /\ length code = code_size xs.
Proof.
  unfold encode_checked. destruct (forallb encodable xs) eqn:Check; try discriminate.
  intro E. inversion E; subst code.
  assert (All : Forall (fun i => encodable i = true) xs).
  { apply Forall_forall. intros i In. now apply forallb_forall with (x := i) in Check. }
  split; [now apply encoded_program_bytes |]. split; [|apply program_length].
  pose proof (encoded_program_layout xs [] All) as Layout. now rewrite app_nil_r in Layout.
Qed.
Definition compile_bytes fs :=
  if valid_program fs then
    match encode_checked (emit_program fs) with
    | Some code => if compilation_check fs code then Some code else None
    | None => None end
  else None.
Theorem compile_bytes_checked fs code : compile_bytes fs = Some code ->
  compilation_check fs code = true /\ Forall (fun b => b < 256) code.
Proof.
  unfold compile_bytes. destruct (valid_program fs); try discriminate.
  destruct (encode_checked (emit_program fs)) eqn:Enc; try discriminate.
  destruct (compilation_check fs l) eqn:C; try discriminate.
  intro E. inversion E; subst l. split; auto.
  exact (proj1 (encode_checked_sound (emit_program fs) code Enc)).
Qed.
