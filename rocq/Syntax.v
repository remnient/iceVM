From Stdlib Require Import List NArith Arith Bool Lia.
Import ListNotations.

Definition modulus : N := 18446744073709551616.
Definition word (x : N) : N := x mod modulus.
Inductive binop := Add | Sub | Mul | Div | And | Or | Xor | Shl | Shr | Eq | Lt.
Definition eval_bin (op : binop) (x y : N) : option N :=
  match op with
  | Add => Some (word (x + y))
  | Sub => Some (word (x + modulus - y))
  | Mul => Some (word (x * y))
  | Div => if N.eqb y 0 then None else Some (N.div x y)
  | And => Some (N.land x y)
  | Or => Some (word (N.lor x y))
  | Xor => Some (word (N.lxor x y))
  | Shl => Some (word (N.shiftl x (N.land y 63)))
  | Shr => Some (N.shiftr x (N.land y 63))
  | Eq => Some (if N.eqb x y then 1 else 0)%N
  | Lt => Some (if N.ltb x y then 1 else 0)%N
  end.
Inductive instr :=
| Halt | Trap | Entry | Ret | Nop | Pad (extra : nat)
| Imm (d : nat) (x : N)
| Move (d a : nat)
| Binary (op : binop) (d a b : nat)
| Load (d a : nat) | Store (a b : nat) | Alloc (d a : nat)
| Mark (d : nat) | Reset (a : nat)
| Jump (target : nat) | Branch (a target : nat)
| Indirect (a : nat) | Call (target : nat).
Definition width (i : instr) : nat :=
  match i with
  | Halt | Trap | Entry | Ret | Nop => 1
  | Pad n => 2 + n
  | Imm _ _ => 10
  | Move _ _ | Load _ _ | Store _ _ | Alloc _ _ => 3
  | Binary _ _ _ _ => 4
  | Mark _ | Reset _ | Indirect _ => 2
  | Jump _ | Call _ => 9
  | Branch _ _ => 10
  end.
Fixpoint little (xs : list nat) : N :=
  match xs with [] => 0%N | x :: xs => (N.of_nat x + 256 * little xs)%N end.
Definition reg (n : nat) := n <? 16.
Definition op_decode (n : nat) : option binop :=
  match n with
  | 16 => Some Add | 17 => Some Sub | 18 => Some Mul | 19 => Some Div
  | 20 => Some And | 21 => Some Or | 22 => Some Xor | 23 => Some Shl
  | 24 => Some Shr | 25 => Some Eq | 26 => Some Lt | _ => None end.
Definition decode (code : list nat) (pc : nat) : option instr :=
  match skipn pc code with
  | 0 :: _ => Some Halt | 1 :: _ => Some Trap
  | 2 :: _ => Some Entry | 3 :: _ => Some Ret | 15 :: _ => Some Nop
  | 27 :: n :: rest => if (n <=? 8) && (n <=? length rest) then Some (Pad n) else None
  | 4 :: d :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: _ =>
      if reg d then Some (Imm d (little [x0;x1;x2;x3;x4;x5;x6;x7])) else None
  | 5 :: d :: a :: _ => if reg d && reg a then Some (Move d a) else None
  | 6 :: d :: a :: _ => if reg d && reg a then Some (Load d a) else None
  | 7 :: a :: b :: _ => if reg a && reg b then Some (Store a b) else None
  | 8 :: d :: a :: _ => if reg d && reg a then Some (Alloc d a) else None
  | 9 :: d :: _ => if reg d then Some (Mark d) else None
  | 10 :: a :: _ => if reg a then Some (Reset a) else None
  | 11 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: _ =>
      Some (Jump (N.to_nat (little [x0;x1;x2;x3;x4;x5;x6;x7])))
  | 12 :: a :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: _ =>
      if reg a then Some (Branch a (N.to_nat (little [x0;x1;x2;x3;x4;x5;x6;x7]))) else None
  | 13 :: a :: _ => if reg a then Some (Indirect a) else None
  | 14 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: _ =>
      Some (Call (N.to_nat (little [x0;x1;x2;x3;x4;x5;x6;x7])))
  | op :: d :: a :: b :: _ =>
      if reg d && reg a && reg b then
        match op_decode op with Some op => Some (Binary op d a b) | None => None end
      else None
  | _ => None end.
