From Stdlib Require Import List NArith Arith Bool.
From IceVM Require Import Syntax State.
Import ListNotations.
Inductive source_comparison := CSame | CDifferent | CBelow | CAtMost | CAbove | CAtLeast.
Definition compare_values op (x y : N) : N :=
  match op with
  | CSame => if N.eqb x y then 1 else 0
  | CDifferent => if N.eqb x y then 0 else 1
  | CBelow => if N.ltb x y then 1 else 0
  | CAtMost => if N.ltb y x then 0 else 1
  | CAbove => if N.ltb y x then 1 else 0
  | CAtLeast => if N.ltb x y then 0 else 1
  end%N.
Inductive expression :=
| Literal (n : N) | Local (name : nat)
| Operation (op : binop) (left right : expression)
| Compare (op : source_comparison) (left right : expression)
| Read (address : expression) | New (size : expression)
| Invoke (function : nat) (argument : expression) | Watermark.
Inductive statement :=
| Skip | Assign (name : nat) (value : expression) | Discard (value : expression)
| Write (address value : expression) | Rewind (value : expression)
| Sequence (first second : statement)
| Conditional (test : expression) (yes no : statement)
| While (test : expression) (body : statement)
| Return (value : expression).
Definition source_program := nat -> option statement.
Inductive control := Evaluate (e : expression) | Value (v : N)
                   | Execute (s : statement) | Returning (v : N).
Inductive continuation :=
| LeftOperand (op : binop) (right : expression)
| RightOperand (op : binop) (left : N)
| LeftComparison (op : source_comparison) (right : expression)
| RightComparison (op : source_comparison) (left : N)
| ReadAddress | NewSize | InvokeArgument (function : nat)
| SaveLocal (name : nat) | WriteAddress (value : expression) | WriteValue (address : N)
| DiscardValue | ResetValue | Choose (yes no : statement)
| Then (next : statement) | Repeat (test : expression) (body : statement)
| ReturnValue | Restore (locals : registers).
Record source_state := SourceState {
  source_control : control;
  locals : registers;
  source_memory : memory;
  source_frontier : nat;
  source_depth : nat;
  continuations : list continuation;
  source_mode : status
}.
Definition source_initial (body : statement) :=
  SourceState (Execute body) (fun _ => 0%N) (fun _ => 0%N) 0 0 [] Running.
Definition source_next (s : source_state) (c : control) (k : list continuation) :=
  SourceState c (locals s) (source_memory s) (source_frontier s) (source_depth s) k Running.
Definition source_fault (s : source_state) (f : fault) :=
  SourceState (source_control s) (locals s) (source_memory s) (source_frontier s)
              (source_depth s) (continuations s) (Fault f).
Definition source_step (program : source_program) (s : source_state) : option source_state :=
  if match source_mode s with Running => true | _ => false end then
  Some (
  match source_control s with
  | Evaluate (Literal n) => source_next s (Value (word n)) (continuations s)
  | Evaluate (Local n) => source_next s (Value (word (locals s n))) (continuations s)
  | Evaluate (Operation op a b) => source_next s (Evaluate a) (LeftOperand op b :: continuations s)
  | Evaluate (Compare op a b) => source_next s (Evaluate a) (LeftComparison op b :: continuations s)
  | Evaluate (Read a) => source_next s (Evaluate a) (ReadAddress :: continuations s)
  | Evaluate (New n) => source_next s (Evaluate n) (NewSize :: continuations s)
  | Evaluate (Invoke f a) => source_next s (Evaluate a) (InvokeArgument f :: continuations s)
  | Evaluate Watermark => source_next s (Value (word (N.of_nat (source_frontier s)))) (continuations s)
  | Execute Skip =>
      match continuations s with
      | Then next :: k => source_next s (Execute next) k
      | Repeat test body :: k => source_next s (Execute (While test body)) k
      | _ => source_fault s Explicit end
  | Execute (Assign n e) => source_next s (Evaluate e) (SaveLocal n :: continuations s)
  | Execute (Discard e) => source_next s (Evaluate e) (DiscardValue :: continuations s)
  | Execute (Write a v) => source_next s (Evaluate a) (WriteAddress v :: continuations s)
  | Execute (Rewind v) => source_next s (Evaluate v) (ResetValue :: continuations s)
  | Execute (Sequence a b) => source_next s (Execute a) (Then b :: continuations s)
  | Execute (Conditional e yes no) => source_next s (Evaluate e) (Choose yes no :: continuations s)
  | Execute (While e body) =>
      source_next s (Evaluate e) (Choose (Sequence body (While e body)) Skip :: continuations s)
  | Execute (Return e) => source_next s (Evaluate e) (ReturnValue :: continuations s)
  | Value v =>
      match continuations s with
      | LeftOperand op b :: k => source_next s (Evaluate b) (RightOperand op v :: k)
      | RightOperand op x :: k =>
          match eval_bin op x v with
          | None => source_fault s Division
          | Some result => source_next s (Value (word result)) k end
      | LeftComparison op b :: k => source_next s (Evaluate b) (RightComparison op v :: k)
      | RightComparison op x :: k => source_next s (Value (compare_values op x v)) k
      | SaveLocal n :: k =>
          SourceState (Execute Skip) (put (locals s) n v) (source_memory s)
                      (source_frontier s) (source_depth s) k Running
      | ReadAddress :: k =>
          let a := N.to_nat v in
          if a + 8 <=? source_frontier s then source_next s (Value (word (read64 (source_memory s) a))) k
          else source_fault s Memory
      | NewSize :: k =>
          let n := N.to_nat v in
          if source_frontier s + n <=? memory_size then
            SourceState (Value (word (N.of_nat (source_frontier s)))) (locals s)
              (clear (source_memory s) (source_frontier s) (source_frontier s + n))
              (source_frontier s + n) (source_depth s) k Running
          else source_fault s Memory
      | WriteAddress e :: k => source_next s (Evaluate e) (WriteValue v :: k)
      | WriteValue a :: k =>
          if N.to_nat a + 8 <=? source_frontier s then
            SourceState (Execute Skip) (locals s) (write64 (source_memory s) (N.to_nat a) v)
                        (source_frontier s) (source_depth s) k Running
          else source_fault s Memory
      | DiscardValue :: k => source_next s (Execute Skip) k
      | ResetValue :: k =>
          if N.to_nat v <=? source_frontier s then
            SourceState (Execute Skip) (locals s) (source_memory s) (N.to_nat v) (source_depth s) k Running
          else source_fault s Region
      | Choose yes no :: k =>
          source_next s (Execute (if N.eqb v 0 then no else yes)) k
      | InvokeArgument f :: k =>
          match program f with
          | None => source_fault s Target
          | Some body =>
              if source_depth s <? stack_size then
                SourceState (Execute body) (put (fun _ => 0%N) 0 v) (source_memory s)
                            (source_frontier s) (S (source_depth s)) (Restore (locals s) :: k) Running
              else source_fault s Stack
          end
      | ReturnValue :: k => source_next s (Returning v) k
      | _ => source_fault s Explicit
      end
  | Returning v =>
      match continuations s with
      | [] => SourceState (Value v) (locals s) (source_memory s) (source_frontier s) 0 [] Stopped
      | Restore caller :: k =>
          SourceState (Value v) caller (source_memory s) (source_frontier s) (pred (source_depth s)) k Running
      | _ :: k => source_next s (Returning v) k
      end
  end)
  else None.
Inductive source_transition program : source_state -> source_state -> Prop :=
| source_transition_step s t : source_step program s = Some t -> source_transition program s t.
Theorem source_deterministic program s a b :
  source_transition program s a -> source_transition program s b -> a = b.
Proof. intros A B. inversion A; inversion B; congruence. Qed.
Inductive source_steps program : source_state -> source_state -> Prop :=
| source_refl s : source_steps program s s
| source_cons s t u : source_transition program s t -> source_steps program t u -> source_steps program s u.
Fixpoint pure_value (env : registers) (e : expression) : option N :=
  match e with
  | Literal n => Some (word n)
  | Local x => Some (word (env x))
  | Operation op a b =>
      match pure_value env a, pure_value env b with
      | Some x, Some y => option_map word (eval_bin op x y)
      | _, _ => None end
  | _ => None end.

Inductive evaluates_expression (program : source_program) :
  nat -> registers -> expression -> memory -> nat -> N -> memory -> nat -> Prop :=
| eval_literal depth env n m h : evaluates_expression program depth env (Literal n) m h (word n) m h
| eval_local depth env n m h : evaluates_expression program depth env (Local n) m h (word (env n)) m h
| eval_operation depth env op a b m h x m1 h1 y m2 h2 z :
    evaluates_expression program depth env a m h x m1 h1 ->
    evaluates_expression program depth env b m1 h1 y m2 h2 -> eval_bin op x y = Some z ->
    evaluates_expression program depth env (Operation op a b) m h (word z) m2 h2
| eval_comparison depth env op a b m h x m1 h1 y m2 h2 :
    evaluates_expression program depth env a m h x m1 h1 ->
    evaluates_expression program depth env b m1 h1 y m2 h2 ->
    evaluates_expression program depth env (Compare op a b) m h (word (compare_values op x y)) m2 h2
| eval_read depth env a m h x m1 h1 :
    evaluates_expression program depth env a m h x m1 h1 -> N.to_nat x + 8 <= h1 ->
    evaluates_expression program depth env (Read a) m h (word (read64 m1 (N.to_nat x))) m1 h1
| eval_new depth env a m h x m1 h1 :
    evaluates_expression program depth env a m h x m1 h1 -> h1 + N.to_nat x <= memory_size ->
    evaluates_expression program depth env (New a) m h (word (N.of_nat h1))
      (clear m1 h1 (h1 + N.to_nat x)) (h1 + N.to_nat x)
| eval_watermark depth env m h : evaluates_expression program depth env Watermark m h (word (N.of_nat h)) m h
| eval_invoke depth env f a body m h x m1 h1 result env2 m2 h2 :
    evaluates_expression program depth env a m h x m1 h1 -> program f = Some body -> f <> 0 ->
    depth < stack_size ->
    evaluates_statement program (S depth) (put (fun _ => 0%N) 0 x) body m1 h1 (Some result) env2 m2 h2 ->
    evaluates_expression program depth env (Invoke f a) m h result m2 h2
with evaluates_statement (program : source_program) :
  nat -> registers -> statement -> memory -> nat -> option N -> registers -> memory -> nat -> Prop :=
| eval_skip depth env m h : evaluates_statement program depth env Skip m h None env m h
| eval_assign depth env n e m h x m1 h1 :
    evaluates_expression program depth env e m h x m1 h1 ->
    evaluates_statement program depth env (Assign n e) m h None (put env n x) m1 h1
| eval_discard depth env e m h x m1 h1 :
    evaluates_expression program depth env e m h x m1 h1 ->
    evaluates_statement program depth env (Discard e) m h None env m1 h1
| eval_write depth env a b m h x m1 h1 y m2 h2 :
    evaluates_expression program depth env a m h x m1 h1 ->
    evaluates_expression program depth env b m1 h1 y m2 h2 -> N.to_nat x + 8 <= h2 ->
    evaluates_statement program depth env (Write a b) m h None env (write64 m2 (N.to_nat x) y) h2
| eval_rewind depth env e m h x m1 h1 :
    evaluates_expression program depth env e m h x m1 h1 -> N.to_nat x <= h1 ->
    evaluates_statement program depth env (Rewind e) m h None env m1 (N.to_nat x)
| eval_sequence_next depth env a b m h env1 m1 h1 result env2 m2 h2 :
    evaluates_statement program depth env a m h None env1 m1 h1 ->
    evaluates_statement program depth env1 b m1 h1 result env2 m2 h2 ->
    evaluates_statement program depth env (Sequence a b) m h result env2 m2 h2
| eval_sequence_return depth env a b m h x env1 m1 h1 :
    evaluates_statement program depth env a m h (Some x) env1 m1 h1 ->
    evaluates_statement program depth env (Sequence a b) m h (Some x) env1 m1 h1
| eval_if_yes depth env e a b m h x m1 h1 result env2 m2 h2 :
    evaluates_expression program depth env e m h x m1 h1 -> x <> 0%N ->
    evaluates_statement program depth env a m1 h1 result env2 m2 h2 ->
    evaluates_statement program depth env (Conditional e a b) m h result env2 m2 h2
| eval_if_no depth env e a b m h m1 h1 result env2 m2 h2 :
    evaluates_expression program depth env e m h 0%N m1 h1 ->
    evaluates_statement program depth env b m1 h1 result env2 m2 h2 ->
    evaluates_statement program depth env (Conditional e a b) m h result env2 m2 h2
| eval_while_done depth env e body m h m1 h1 :
    evaluates_expression program depth env e m h 0%N m1 h1 ->
    evaluates_statement program depth env (While e body) m h None env m1 h1
| eval_while_next depth env e body m h x m1 h1 env1 m2 h2 result env2 m3 h3 :
    evaluates_expression program depth env e m h x m1 h1 -> x <> 0%N ->
    evaluates_statement program depth env body m1 h1 None env1 m2 h2 ->
    evaluates_statement program depth env1 (While e body) m2 h2 result env2 m3 h3 ->
    evaluates_statement program depth env (While e body) m h result env2 m3 h3
| eval_while_return depth env e body m h x m1 h1 result env1 m2 h2 :
    evaluates_expression program depth env e m h x m1 h1 -> x <> 0%N ->
    evaluates_statement program depth env body m1 h1 (Some result) env1 m2 h2 ->
    evaluates_statement program depth env (While e body) m h (Some result) env1 m2 h2
| eval_return depth env e m h x m1 h1 :
    evaluates_expression program depth env e m h x m1 h1 ->
    evaluates_statement program depth env (Return e) m h (Some x) env m1 h1.
Scheme expression_evaluation_ind := Induction for evaluates_expression Sort Prop
with statement_evaluation_ind := Induction for evaluates_statement Sort Prop.
Combined Scheme evaluation_ind from expression_evaluation_ind, statement_evaluation_ind.

Inductive configuration :=
| Expression (depth : nat) (env : registers) (e : expression) (m : memory) (h : nat)
| Statement (depth : nat) (env : registers) (body : statement) (m : memory) (h : nat).
Inductive descends (program : source_program) : configuration -> configuration -> Prop :=
| descend_operation_left d env op a b m h :
    descends program (Expression d env (Operation op a b) m h) (Expression d env a m h)
| descend_operation_right d env op a b m h x m1 h1 :
    evaluates_expression program d env a m h x m1 h1 ->
    descends program (Expression d env (Operation op a b) m h) (Expression d env b m1 h1)
| descend_comparison_left d env op a b m h :
    descends program (Expression d env (Compare op a b) m h) (Expression d env a m h)
| descend_comparison_right d env op a b m h x m1 h1 :
    evaluates_expression program d env a m h x m1 h1 ->
    descends program (Expression d env (Compare op a b) m h) (Expression d env b m1 h1)
| descend_read d env a m h :
    descends program (Expression d env (Read a) m h) (Expression d env a m h)
| descend_new d env a m h :
    descends program (Expression d env (New a) m h) (Expression d env a m h)
| descend_argument d env f a m h :
    descends program (Expression d env (Invoke f a) m h) (Expression d env a m h)
| descend_function d env f a body m h x m1 h1 :
    evaluates_expression program d env a m h x m1 h1 -> program f = Some body ->
    f <> 0 -> d < stack_size ->
    descends program (Expression d env (Invoke f a) m h)
                     (Statement (S d) (put (fun _ => 0%N) 0 x) body m1 h1)
| descend_assign d env n e m h :
    descends program (Statement d env (Assign n e) m h) (Expression d env e m h)
| descend_discard d env e m h :
    descends program (Statement d env (Discard e) m h) (Expression d env e m h)
| descend_write_address d env a b m h :
    descends program (Statement d env (Write a b) m h) (Expression d env a m h)
| descend_write_value d env a b m h x m1 h1 :
    evaluates_expression program d env a m h x m1 h1 ->
    descends program (Statement d env (Write a b) m h) (Expression d env b m1 h1)
| descend_rewind d env e m h :
    descends program (Statement d env (Rewind e) m h) (Expression d env e m h)
| descend_sequence_first d env a b m h :
    descends program (Statement d env (Sequence a b) m h) (Statement d env a m h)
| descend_sequence_next d env a b m h env1 m1 h1 :
    evaluates_statement program d env a m h None env1 m1 h1 ->
    descends program (Statement d env (Sequence a b) m h) (Statement d env1 b m1 h1)
| descend_condition d env e a b m h :
    descends program (Statement d env (Conditional e a b) m h) (Expression d env e m h)
| descend_condition_body d env e a b m h x m1 h1 :
    evaluates_expression program d env e m h x m1 h1 ->
    descends program (Statement d env (Conditional e a b) m h)
                     (Statement d env (if N.eqb x 0 then b else a) m1 h1)
| descend_while_test d env e body m h :
    descends program (Statement d env (While e body) m h) (Expression d env e m h)
| descend_while_body d env e body m h x m1 h1 :
    evaluates_expression program d env e m h x m1 h1 -> x <> 0%N ->
    descends program (Statement d env (While e body) m h) (Statement d env body m1 h1)
| descend_while_next d env e body m h x m1 h1 env1 m2 h2 :
    evaluates_expression program d env e m h x m1 h1 -> x <> 0%N ->
    evaluates_statement program d env body m1 h1 None env1 m2 h2 ->
    descends program (Statement d env (While e body) m h) (Statement d env1 (While e body) m2 h2)
| descend_return d env e m h :
    descends program (Statement d env (Return e) m h) (Expression d env e m h).
Inductive local_fault (program : source_program) : configuration -> fault -> memory -> nat -> Prop :=
| fault_operation d env op a b m h x m1 h1 y m2 h2 :
    evaluates_expression program d env a m h x m1 h1 ->
    evaluates_expression program d env b m1 h1 y m2 h2 -> eval_bin op x y = None ->
    local_fault program (Expression d env (Operation op a b) m h) Division m2 h2
| fault_read d env a m h x m1 h1 :
    evaluates_expression program d env a m h x m1 h1 -> h1 < N.to_nat x + 8 ->
    local_fault program (Expression d env (Read a) m h) Memory m1 h1
| fault_new d env a m h x m1 h1 :
    evaluates_expression program d env a m h x m1 h1 -> memory_size < h1 + N.to_nat x ->
    local_fault program (Expression d env (New a) m h) Memory m1 h1
| fault_stack d env f a body m h x m1 h1 :
    evaluates_expression program d env a m h x m1 h1 -> program f = Some body -> f <> 0 ->
    stack_size <= d -> local_fault program (Expression d env (Invoke f a) m h) Stack m1 h1
| fault_write d env a b m h x m1 h1 y m2 h2 :
    evaluates_expression program d env a m h x m1 h1 ->
    evaluates_expression program d env b m1 h1 y m2 h2 -> h2 < N.to_nat x + 8 ->
    local_fault program (Statement d env (Write a b) m h) Memory m2 h2
| fault_rewind d env e m h x m1 h1 :
    evaluates_expression program d env e m h x m1 h1 -> h1 < N.to_nat x ->
    local_fault program (Statement d env (Rewind e) m h) Region m1 h1.
Inductive raises program : configuration -> fault -> memory -> nat -> Prop :=
| raises_here c f m h : local_fault program c f m h -> raises program c f m h
| raises_below c child f m h : descends program c child -> raises program child f m h -> raises program c f m h.
CoInductive source_diverges program : configuration -> Prop :=
| diverges_below c child : descends program c child -> source_diverges program child -> source_diverges program c.
Fixpoint expression_rank e :=
  match e with
  | Literal _ | Local _ | Watermark => 1
  | Operation _ a b | Compare _ a b => S (expression_rank a + expression_rank b)
  | Read a | New a | Invoke _ a => S (expression_rank a) end.
Fixpoint statement_rank body :=
  match body with
  | Skip => 1
  | Assign _ e | Discard e | Rewind e | Return e => S (expression_rank e)
  | Write a b => S (expression_rank a + expression_rank b)
  | Sequence a b => S (statement_rank a + statement_rank b)
  | Conditional e a b => S (expression_rank e + statement_rank a + statement_rank b)
  | While e body => S (expression_rank e + statement_rank body) end.
Definition configuration_rank c :=
  match c with Expression _ _ e _ _ => expression_rank e | Statement _ _ body _ _ => statement_rank body end.
