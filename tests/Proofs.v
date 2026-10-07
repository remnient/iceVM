From Stdlib Require Import List NArith String Ascii.
From Loosevm Require Import Syntax State Interpreter Source Compiler Encoding Frontend Simulation Optimisation TotalSimulation Forward.
Import ListNotations.
Definition normal_code : list nat := [2;4;9;42;0;0;0;0;0;0;0;5;0;9;0].
Definition division_code : list nat := [2;4;9;1;0;0;0;0;0;0;0;4;10;0;0;0;0;0;0;0;0;19;9;9;10;5;0;9;0].
Definition memory_code : list nat := [2;4;9;0;0;0;0;0;0;0;0;6;9;9;5;0;9;0].
Definition loop_code : list nat := [2;4;9;1;0;0;0;0;0;0;0;12;9;30;0;0;0;0;0;0;0;11;39;0;0;0;0;0;0;0;11;1;0;0;0;0;0;0;0;4;9;0;0;0;0;0;0;0;0;5;0;9;0].
Definition normal_main := Return (Literal 42%N).
Definition division_main := Return (Operation Div (Literal 1%N) (Literal 0%N)).
Definition memory_main := Return (Read (Literal 0%N)).
Definition loop_main := Sequence (While (Literal 1%N) Skip) (Return (Literal 0%N)).
Example normal_checked : compilation_check [normal_main] normal_code = true.
Proof. vm_compute. reflexivity. Qed.
Example division_checked : compilation_check [division_main] division_code = true.
Proof. vm_compute. reflexivity. Qed.
Example memory_checked : compilation_check [memory_main] memory_code = true.
Proof. vm_compute. reflexivity. Qed.
Example loop_checked : compilation_check [loop_main] loop_code = true.
Proof. vm_compute. reflexivity. Qed.
Example normal_compilation : exists t, steps normal_code initial t /\ mode t = Stopped /\ regs t 0 = 42%N.
Proof.
  destruct (compiled_program_terminates [normal_main] normal_code normal_main 42%N
    (fun _ => 0%N) (fun _ => 0%N) 0 normal_checked eq_refl
    (eval_return _ _ _ _ _ _ _ _ _ (eval_literal _ _ _ _ _ _))) as [t [T [M [R _]]]].
  exists t. auto.
Qed.
Example division_raises : raises (source_lookup [division_main])
  (Statement 0 (fun _ => 0%N) division_main (fun _ => 0%N) 0) Division (fun _ => 0%N) 0.
Proof.
  eapply raises_below; [apply descend_return |]. apply raises_here.
  eapply fault_operation with (x := 1%N) (y := 0%N); try apply eval_literal; reflexivity.
Qed.
Example division_compilation : fault_run division_code initial Division (fun _ => 0%N) 0.
Proof. eapply compiled_program_faults; [exact division_checked | reflexivity | exact division_raises]. Qed.
Example memory_raises : raises (source_lookup [memory_main])
  (Statement 0 (fun _ => 0%N) memory_main (fun _ => 0%N) 0) Memory (fun _ => 0%N) 0.
Proof.
  eapply raises_below; [apply descend_return |]. apply raises_here.
  eapply fault_read with (x := 0%N); [apply eval_literal | repeat constructor].
Qed.
Example memory_compilation : fault_run memory_code initial Memory (fun _ => 0%N) 0.
Proof. eapply compiled_program_faults; [exact memory_checked | reflexivity | exact memory_raises]. Qed.
Example loop_diverges : source_diverges (source_lookup [loop_main])
  (Statement 0 (fun _ => 0%N) loop_main (fun _ => 0%N) 0).
Proof. eapply diverges_below; [apply descend_sequence_first | apply source_infinite_loop]. Qed.
Example loop_compilation : diverges loop_code.
Proof. eapply compiled_program_diverges; [exact loop_checked | reflexivity | exact loop_diverges]. Qed.
Example loop_execution : infinite_steps loop_code initial.
Proof. apply running_forever. exact loop_compilation. Qed.
Example loop_source_execution : source_infinite_steps (source_lookup [loop_main]) (source_initial loop_main).
Proof. exact (source_divergence_infinite _ _ [] loop_diverges). Qed.
Example fallthrough_rejected : compilation_check [Skip] [2;0] = false.
Proof. vm_compute. reflexivity. Qed.
Example normal_encoded : compile_bytes [normal_main] = Some normal_code.
Proof. vm_compute. reflexivity. Qed.
Example division_encoded : compile_bytes [division_main] = Some division_code.
Proof. vm_compute. reflexivity. Qed.
Example loop_encoded : compile_bytes [loop_main] = Some loop_code.
Proof. vm_compute. reflexivity. Qed.

Definition codes text := map nat_of_ascii (list_ascii_of_string text).
Definition return_certificate e := [FunctionCertificate keyword_main None
  (CertificateThen (CertificateReturn e) CertificateEnd)].
Definition literal_text := codes "def main():
    return 42
".
Example text_literal_checked : exists code,
  compile_text literal_text (return_certificate (CertificateLiteral 42)) = Some code.
Proof. vm_compute. eexists. reflexivity. Qed.
Example text_literal_mismatch_rejected :
  compile_text literal_text (return_certificate (CertificateLiteral 41)) = None.
Proof. vm_compute. reflexivity. Qed.
Definition precedence_text := codes "def main():
    return 1 + 2 * 3
".
Example text_precedence_checked : exists code, compile_text precedence_text
  (return_certificate (CertificateBinary Add (CertificateLiteral 1)
    (CertificateBinary Mul (CertificateLiteral 2) (CertificateLiteral 3)))) = Some code.
Proof. vm_compute. eexists. reflexivity. Qed.
Example text_precedence_forgery_rejected : compile_text precedence_text
  (return_certificate (CertificateBinary Mul (CertificateBinary Add (CertificateLiteral 1)
    (CertificateLiteral 2)) (CertificateLiteral 3))) = None.
Proof. vm_compute. reflexivity. Qed.
Example text_omission_rejected : compile_text (literal_text ++ codes "    return 9
") (return_certificate (CertificateLiteral 42)) = None.
Proof. vm_compute. reflexivity. Qed.
Example empty_hex_rejected : numeral [48;120] = None.
Proof. reflexivity. Qed.
Definition crlf_text := flat_map (fun c => if Nat.eqb c 10 then [13;10] else [c]) literal_text.
Definition bare_cr_text := map (fun c => if Nat.eqb c 10 then 13 else c) literal_text.
Example crlf_text_checked : exists code,
  compile_text crlf_text (return_certificate (CertificateLiteral 42)) = Some code.
Proof. vm_compute. eexists. reflexivity. Qed.
Example bare_cr_text_rejected : compile_text bare_cr_text (return_certificate (CertificateLiteral 42)) = None.
Proof. vm_compute. reflexivity. Qed.

Definition interior_pc_code : list nat := [2;27;8;11;0;0;0;0;0;0;0;0].
Definition interior_pc_state := State 3 (fun _ => 0%N) (fun _ => 0%N) 0 [] Running.
Example interior_pc_jump_traps : step interior_pc_code interior_pc_state =
  Some (finish interior_pc_state (Fault Target)).
Proof. vm_compute. reflexivity. Qed.

Example interior_pc_program_verified : Verifier.verify interior_pc_code = true.
Proof. vm_compute. reflexivity. Qed.

Example normal_cek_simulation :
  forward_simulation (source_transition (source_lookup [normal_main])) normal_code
    (cek_matches [normal_main] normal_code).
Proof. now apply compiler_cek_simulation. Qed.
Example normal_cek_result : exists t, steps normal_code initial t /\ mode t = Stopped /\ regs t 0 = 42%N.
Proof.
  destruct (compiler_cek_termination [normal_main] normal_code normal_main
    (SourceState (Value 42%N) (fun _ => 0%N) (fun _ => 0%N) 0 0 [] Stopped) 42%N
    normal_checked eq_refl) as [t [Steps [Mode [Value Rest]]]].
  - eapply source_program_normal. apply eval_return. apply eval_literal.
  - reflexivity.
  - reflexivity.
  - exists t. auto.
Qed.
Example loop_cek_execution : infinite_steps loop_code initial.
Proof.
  eapply compiler_cek_divergence; [exact loop_checked | | exact loop_source_execution].
  now apply compiler_cek_initial.
Qed.
Example checked_text_cek_simulation code :
  compile_text literal_text (return_certificate (CertificateLiteral 42)) = Some code ->
  exists fs, check_frontend literal_text (return_certificate (CertificateLiteral 42)) = Some fs /\
    forward_simulation (source_transition (source_lookup fs)) code (cek_matches fs code).
Proof.
  intro Compiled. destruct (text_forward_simulation _ _ _ Compiled) as [fs [Frontend [Simulation Rest]]].
  exists fs. auto.
Qed.
