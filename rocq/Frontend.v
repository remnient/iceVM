From Stdlib Require Import List Arith NArith Bool Lia.
From IceVM Require Import Syntax Source Compiler Encoding.
Import ListNotations.
Definition name := list nat.
Definition name_eqb (a b : name) := if list_eq_dec Nat.eq_dec a b then true else false.
Lemma name_eqb_spec a b : name_eqb a b = true <-> a = b.
Proof. unfold name_eqb. destruct (list_eq_dec Nat.eq_dec a b); intuition discriminate. Qed.
Definition ascii_range lo hi c := (lo <=? c) && (c <=? hi).
Definition letter c := ascii_range 65 90 c || ascii_range 97 122 c || Nat.eqb c 95.
Definition digit c := ascii_range 48 57 c.
Definition word_char c := letter c || digit c.
Definition inline_space c := Nat.eqb c 32 || Nat.eqb c 9 || Nat.eqb c 13.
Fixpoint span (test : nat -> bool) xs : list nat * list nat :=
  match xs with
  | [] => ([], [])
  | x :: xs => if test x then let '(yes, rest) := span test xs in (x :: yes, rest) else ([], x :: xs)
  end.
Lemma span_sound test xs yes rest : span test xs = (yes, rest) ->
  xs = yes ++ rest /\ Forall (fun c => test c = true) yes /\
  (rest = [] \/ exists c tail, rest = c :: tail /\ test c = false).
Proof.
  revert yes rest. induction xs; intros yes rest E; cbn [span] in E.
  - inversion E; subst. repeat split; auto.
  - destruct (test a) eqn:A.
    + destruct (span test xs) as [prefix suffix] eqn:S. inversion E; subst.
      destruct (IHxs _ _ eq_refl) as [Shape [All End]]. split; [cbn; now rewrite Shape |].
      split; [constructor; assumption | assumption].
    + inversion E; subst. split; [reflexivity |]. split; [constructor |]. right. eauto.
Qed.
Lemma span_length test xs yes rest : span test xs = (yes, rest) -> length rest <= length xs.
Proof. intro E. apply span_sound in E. destruct E as [E _]. rewrite E, length_app. lia. Qed.
Definition numeral_digit c : option N :=
  if digit c then Some (N.of_nat (c - 48))
  else if ascii_range 65 70 c then Some (N.of_nat (c - 55))
  else if ascii_range 97 102 c then Some (N.of_nat (c - 87)) else None.
Fixpoint digits_value (base acc : N) xs : option N :=
  match xs with
  | [] => Some acc
  | c :: xs => if Nat.eqb c 95 then digits_value base acc xs else
      match numeral_digit c with
      | Some v => if N.ltb v base then digits_value base (base * acc + v)%N xs else None
      | None => None end
  end.
Fixpoint digit_sequence base previous xs :=
  match xs with
  | [] => previous
  | c :: xs => if Nat.eqb c 95 then previous && digit_sequence base false xs else
      match numeral_digit c with Some v => N.ltb v base && digit_sequence base true xs | None => false end
  end.
Definition checked_digits base prefix_separator xs :=
  match xs with [] => None | _ => if digit_sequence base prefix_separator xs then digits_value base 0 xs else None end.
Definition numeral xs :=
  match xs with
  | [] => None
  | 48 :: 120 :: rest | 48 :: 88 :: rest => checked_digits 16 true rest
  | 48 :: 111 :: rest | 48 :: 79 :: rest => checked_digits 8 true rest
  | 48 :: 98 :: rest | 48 :: 66 :: rest => checked_digits 2 true rest
  | 48 :: _ => match checked_digits 10 false xs with Some n => if N.eqb n 0 then Some n else None | None => None end
  | _ => checked_digits 10 false xs end.

Inductive token := Name (text : name) | Number (value : N) | Symbol (text : name).
Definition token_eq_dec (a b : token) : {a = b} + {a <> b}.
Proof. decide equality; try apply N.eq_dec; apply list_eq_dec; apply Nat.eq_dec. Defined.
Definition token_eqb a b := if token_eq_dec a b then true else false.
Definition operator_pair a b :=
  (Nat.eqb a 47 && Nat.eqb b 47) || (Nat.eqb a 60 && Nat.eqb b 60) ||
  (Nat.eqb a 62 && Nat.eqb b 62) ||
  ((Nat.eqb a 60 || Nat.eqb a 62 || Nat.eqb a 61 || Nat.eqb a 33) && Nat.eqb b 61).
Definition operator_single c := existsb (Nat.eqb c) [40;41;44;58;61;43;45;42;38;124;94;60;62;126].
Fixpoint lex fuel chars : option (list token) :=
  match chars with
  | [] => Some []
  | c :: chars =>
      match fuel with
      | 0 => None
      | S fuel =>
          if inline_space c then lex fuel chars
          else if Nat.eqb c 35 then Some []
          else if letter c then
            let '(tail, rest) := span word_char chars in
            option_map (cons (Name (c :: tail))) (lex fuel rest)
          else if digit c then
            let '(tail, rest) := span word_char chars in
            match numeral (c :: tail) with
            | Some n => option_map (cons (Number n)) (lex fuel rest)
            | None => None end
          else match chars with
          | d :: rest =>
              if operator_pair c d then option_map (cons (Symbol [c;d])) (lex fuel rest)
              else if operator_single c then option_map (cons (Symbol [c])) (lex fuel chars)
              else None
          | [] => if operator_single c then Some [Symbol [c]] else None end
      end end.
Inductive lexes : list nat -> list token -> Prop :=
| lexes_empty : lexes [] []
| lexes_space c chars tokens : inline_space c = true -> lexes chars tokens -> lexes (c :: chars) tokens
| lexes_comment chars : lexes (35 :: chars) []
| lexes_name c tail rest tokens : letter c = true -> Forall (fun x => word_char x = true) tail ->
    (rest = [] \/ exists x xs, rest = x :: xs /\ word_char x = false) ->
    lexes rest tokens -> lexes ((c :: tail) ++ rest) (Name (c :: tail) :: tokens)
| lexes_number c tail rest n tokens : digit c = true -> Forall (fun x => word_char x = true) tail ->
    (rest = [] \/ exists x xs, rest = x :: xs /\ word_char x = false) ->
    numeral (c :: tail) = Some n -> lexes rest tokens ->
    lexes ((c :: tail) ++ rest) (Number n :: tokens)
| lexes_pair c d rest tokens : operator_pair c d = true -> lexes rest tokens ->
    lexes (c :: d :: rest) (Symbol [c;d] :: tokens)
| lexes_single c rest tokens : operator_single c = true ->
    (rest = [] \/ exists d xs, rest = d :: xs /\ operator_pair c d = false) ->
    lexes rest tokens -> lexes (c :: rest) (Symbol [c] :: tokens).
Theorem lex_sound fuel chars tokens : lex fuel chars = Some tokens -> lexes chars tokens.
Proof.
  revert chars tokens. induction fuel; intros chars tokens E;
    destruct chars as [|c chars]; cbn [lex] in E; try discriminate.
  - inversion E; constructor.
  - inversion E; constructor.
  - destruct (inline_space c) eqn:Space; [eapply lexes_space; eauto |].
    destruct (Nat.eqb c 35) eqn:Comment.
    + apply Nat.eqb_eq in Comment. subst c. inversion E; apply lexes_comment.
    + destruct (letter c) eqn:Letter.
      * destruct (span word_char chars) as [tail rest] eqn:Span.
        destruct (lex fuel rest) eqn:Rest; inversion E; subst.
        destruct (span_sound word_char chars tail rest Span) as [Shape [All End]]. rewrite Shape.
        eapply lexes_name; eauto.
      * destruct (digit c) eqn:Digit.
        -- destruct (span word_char chars) as [tail rest] eqn:Span.
           destruct (numeral (c :: tail)) eqn:Num; try discriminate.
           destruct (lex fuel rest) eqn:Rest; inversion E; subst.
           destruct (span_sound word_char chars tail rest Span) as [Shape [All End]]. rewrite Shape.
           eapply lexes_number; eauto.
        -- destruct chars as [|d rest].
           ++ destruct (operator_single c) eqn:Single; inversion E; subst.
              eapply lexes_single; eauto; constructor.
           ++ destruct (operator_pair c d) eqn:Pair.
              ** destruct (lex fuel rest) eqn:Rest; inversion E; subst. eapply lexes_pair; eauto.
              ** destruct (operator_single c) eqn:Single; try discriminate.
                 destruct (lex fuel (d :: rest)) eqn:Rest; inversion E; subst.
                 eapply lexes_single; eauto.
Qed.
Definition keyword_main : name := [109;97;105;110].
Definition keyword_mark : name := [109;97;114;107].
Definition keyword_load : name := [108;111;97;100].
Definition keyword_alloc : name := [97;108;108;111;99].
Definition keyword_store : name := [115;116;111;114;101].
Definition keyword_reset : name := [114;101;115;101;116].
Definition keyword_true : name := [84;114;117;101].
Definition keyword_false : name := [70;97;108;115;101].
Definition reserved : list name := [
  [70;97;108;115;101];[78;111;110;101];[84;114;117;101];[97;110;100];
  [97;115];[97;115;115;101;114;116];[97;115;121;110;99];[97;119;97;105;116];
  [98;114;101;97;107];[99;108;97;115;115];[99;111;110;116;105;110;117;101];[100;101;102];
  [100;101;108];[101;108;105;102];[101;108;115;101];[101;120;99;101;112;116];
  [102;105;110;97;108;108;121];[102;111;114];[102;114;111;109];[103;108;111;98;97;108];
  [105;102];[105;109;112;111;114;116];[105;110];[105;115];
  [108;97;109;98;100;97];[110;111;110;108;111;99;97;108];[110;111;116];[111;114];
  [112;97;115;115];[114;97;105;115;101];[114;101;116;117;114;110];[116;114;121];
  [119;104;105;108;101];[119;105;116;104];[121;105;101;108;100]].

Definition valid_name n :=
  match n with [] => false | c :: rest => letter c && forallb word_char rest && negb (existsb (name_eqb n) reserved) end.
Fixpoint name_index n names :=
  match names with [] => None | x :: xs => if name_eqb n x then Some 0 else option_map S (name_index n xs) end.
Definition consume t tokens :=
  match tokens with [] => None | x :: xs => if token_eqb t x then Some xs else None end.
Lemma consume_sound t tokens rest : consume t tokens = Some rest -> tokens = t :: rest.
Proof.
  destruct tokens as [|x xs]; cbn [consume]; try discriminate.
  unfold token_eqb. destruct (token_eq_dec t x); intro E; try discriminate. inversion E; congruence.
Qed.
Definition binary_syntax op : option (name * nat) :=
  match op with
  | Add => Some ([43], 7) | Sub => Some ([45], 7) | Mul => Some ([42], 8) | Div => Some ([47;47], 8)
  | And => Some ([38], 5) | Or => Some ([124], 3) | Xor => Some ([94], 4)
  | Shl => Some ([60;60], 6) | Shr => Some ([62;62], 6) | _ => None end.
Definition comparison_syntax op : name :=
  match op with CSame => [61;61] | CDifferent => [33;61] | CBelow => [60]
  | CAtMost => [60;61] | CAbove => [62] | CAtLeast => [62;61] end.
Inductive unary := Negative | Complement | LogicalNot.
Definition unary_token u := match u with Negative => Symbol [45] | Complement => Symbol [126] | LogicalNot => Name [110;111;116] end.
Definition unary_precedence u := match u with LogicalNot => 1 | _ => 9 end.
Definition unary_expression u e :=
  match u with
  | Negative => Operation Sub (Literal 0%N) e
  | Complement => Operation Xor (Literal 18446744073709551615%N) e
  | LogicalNot => Operation Eq e (Literal 0%N) end.
Inductive expression_certificate :=
| CertificateLiteral (n : N) | CertificateBoolean (b : bool) | CertificateName (n : name)
| CertificateBinary (op : binop) (a b : expression_certificate)
| CertificateComparison (op : source_comparison) (a b : expression_certificate)
| CertificateUnary (u : unary) (a : expression_certificate)
| CertificateParenthesis (a : expression_certificate)
| CertificateCallZero (f : name) | CertificateCallOne (f : name) (a : expression_certificate).
Definition call_expression functions f e :=
  if name_eqb f keyword_load then Some (Read e)
  else if name_eqb f keyword_alloc then Some (New e)
  else match name_index f functions with
  | Some n => if 0 <? n then Some (Invoke n e) else None | None => None end.
Local Notation "'let?' p ':=' value 'in' body" :=
  (match value with Some p => body | None => None end)
  (at level 200, p pattern, value at level 100, body at level 200).
Fixpoint check_expression locals functions precedence cert tokens : option (expression * list token) :=
  match cert with
  | CertificateLiteral n => let? rest := consume (Number n) tokens in Some (Literal (word n), rest)
  | CertificateBoolean b =>
      let? rest := consume (Name (if b then keyword_true else keyword_false)) tokens in
      Some (Literal (if b then 1 else 0)%N, rest)
  | CertificateName n =>
      if valid_name n then
        let? slot := name_index n locals in let? rest := consume (Name n) tokens in Some (Local slot, rest)
      else None
  | CertificateBinary op a b =>
      let? (symbol, p) := binary_syntax op in
      if precedence <=? p then
        let? (lhs, rest) := check_expression locals functions p a tokens in
        let? rest := consume (Symbol symbol) rest in
        let? (rhs, rest) := check_expression locals functions (S p) b rest in
        Some (Operation op lhs rhs, rest)
      else None
  | CertificateComparison op a b =>
      if precedence <=? 2 then
        let? (lhs, rest) := check_expression locals functions 3 a tokens in
        let? rest := consume (Symbol (comparison_syntax op)) rest in
        let? (rhs, rest) := check_expression locals functions 3 b rest in
        Some (Compare op lhs rhs, rest)
      else None
  | CertificateUnary u a =>
      if precedence <=? unary_precedence u then
        let? rest := consume (unary_token u) tokens in
        let? (e, rest) := check_expression locals functions (unary_precedence u) a rest in
        Some (unary_expression u e, rest)
      else None
  | CertificateParenthesis a =>
      let? rest := consume (Symbol [40]) tokens in
      let? (e, rest) := check_expression locals functions 0 a rest in
      let? rest := consume (Symbol [41]) rest in Some (e, rest)
  | CertificateCallZero f =>
      if name_eqb f keyword_mark then
        let? rest := consume (Name f) tokens in
        let? rest := consume (Symbol [40]) rest in
        let? rest := consume (Symbol [41]) rest in Some (Watermark, rest)
      else None
  | CertificateCallOne f a =>
      let? rest := consume (Name f) tokens in
      let? rest := consume (Symbol [40]) rest in
      let? (e, rest) := check_expression locals functions 0 a rest in
      let? rest := consume (Symbol [41]) rest in
      let? e := call_expression functions f e in Some (e, rest)
  end.
Inductive parses_expression locals functions : nat -> list token -> expression -> list token -> Prop :=
| parses_literal p n rest : parses_expression locals functions p (Number n :: rest) (Literal (word n)) rest
| parses_boolean p (b : bool) rest : parses_expression locals functions p
    (Name (if b then keyword_true else keyword_false) :: rest) (Literal (if b then 1 else 0)%N) rest
| parses_name p n slot rest : valid_name n = true -> name_index n locals = Some slot ->
    parses_expression locals functions p (Name n :: rest) (Local slot) rest
| parses_binary p op symbol level first lhs middle rhs rest : binary_syntax op = Some (symbol, level) -> p <= level ->
    parses_expression locals functions level first lhs (Symbol symbol :: middle) ->
    parses_expression locals functions (S level) middle rhs rest ->
    parses_expression locals functions p first (Operation op lhs rhs) rest
| parses_comparison p op first lhs middle rhs rest : p <= 2 ->
    parses_expression locals functions 3 first lhs (Symbol (comparison_syntax op) :: middle) ->
    parses_expression locals functions 3 middle rhs rest ->
    parses_expression locals functions p first (Compare op lhs rhs) rest
| parses_unary p u first e rest : p <= unary_precedence u ->
    parses_expression locals functions (unary_precedence u) first e rest ->
    parses_expression locals functions p (unary_token u :: first) (unary_expression u e) rest
| parses_parenthesis p first e rest : parses_expression locals functions 0 first e (Symbol [41] :: rest) ->
    parses_expression locals functions p (Symbol [40] :: first) e rest
| parses_mark p rest : parses_expression locals functions p (Name keyword_mark :: Symbol [40] :: Symbol [41] :: rest) Watermark rest
| parses_call p f first e result rest : parses_expression locals functions 0 first e (Symbol [41] :: rest) ->
    call_expression functions f e = Some result ->
    parses_expression locals functions p (Name f :: Symbol [40] :: first) result rest.
Theorem check_expression_sound locals functions cert : forall p tokens e rest,
  check_expression locals functions p cert tokens = Some (e, rest) ->
  parses_expression locals functions p tokens e rest.
Proof.
  induction cert; intros p tokens e rest E; cbn [check_expression] in E.
  - destruct (consume (Number n) tokens) eqn:C; try discriminate. inversion E; subst.
    apply consume_sound in C. subst tokens. constructor.
  - destruct (consume (Name (if b then keyword_true else keyword_false)) tokens) eqn:C; try discriminate.
    inversion E; subst. apply consume_sound in C. subst tokens. constructor.
  - destruct (valid_name n) eqn:V; try discriminate. destruct (name_index n locals) eqn:I; try discriminate.
    destruct (consume (Name n) tokens) eqn:C; try discriminate. inversion E; subst.
    apply consume_sound in C. subst tokens. now constructor.
  - destruct (binary_syntax op) as [[symbol level]|] eqn:B; try discriminate.
    destruct (p <=? level) eqn:P; try discriminate. apply Nat.leb_le in P.
    destruct (check_expression locals functions level cert1 tokens) as [[lhs middle]|] eqn:L; try discriminate.
    destruct (consume (Symbol symbol) middle) eqn:C; try discriminate.
    destruct (check_expression locals functions (S level) cert2 l) as [[rhs after]|] eqn:R; try discriminate.
    inversion E; subst. apply consume_sound in C. subst middle.
    eapply parses_binary; eauto.
  - destruct (p <=? 2) eqn:P; try discriminate. apply Nat.leb_le in P.
    destruct (check_expression locals functions 3 cert1 tokens) as [[lhs middle]|] eqn:L; try discriminate.
    destruct (consume (Symbol (comparison_syntax op)) middle) eqn:C; try discriminate.
    destruct (check_expression locals functions 3 cert2 l) as [[rhs after]|] eqn:R; try discriminate.
    inversion E; subst. apply consume_sound in C. subst middle. eapply parses_comparison; eauto.
  - destruct (p <=? unary_precedence u) eqn:P; try discriminate. apply Nat.leb_le in P.
    destruct (consume (unary_token u) tokens) eqn:C; try discriminate.
    destruct (check_expression locals functions (unary_precedence u) cert l) as [[value after]|] eqn:R; try discriminate.
    inversion E; subst. apply consume_sound in C. subst tokens. eapply parses_unary; eauto.
  - destruct (consume (Symbol [40]) tokens) eqn:C; try discriminate.
    destruct (check_expression locals functions 0 cert l) as [[value middle]|] eqn:R; try discriminate.
    destruct (consume (Symbol [41]) middle) eqn:Close; try discriminate.
    inversion E; subst. apply consume_sound in C, Close. subst tokens middle. constructor. now apply IHcert.
  - destruct (name_eqb f keyword_mark) eqn:F; try discriminate. apply name_eqb_spec in F. subst f.
    destruct (consume (Name keyword_mark) tokens) eqn:C; try discriminate.
    destruct (consume (Symbol [40]) l) eqn:Open; try discriminate.
    destruct (consume (Symbol [41]) l0) eqn:Close; try discriminate.
    inversion E; subst. apply consume_sound in C, Open, Close. subst tokens l l0. constructor.
  - destruct (consume (Name f) tokens) eqn:C; try discriminate.
    destruct (consume (Symbol [40]) l) eqn:Open; try discriminate.
    destruct (check_expression locals functions 0 cert l0) as [[value middle]|] eqn:R; try discriminate.
    destruct (consume (Symbol [41]) middle) eqn:Close; try discriminate.
    destruct (call_expression functions f value) eqn:Call; try discriminate.
    inversion E; subst. apply consume_sound in C, Open, Close. subst tokens l middle. eapply parses_call; eauto.
Qed.
Record source_line := SourceLine { indentation : nat; line_tokens : list token }.
Fixpoint text_lines chars :=
  match chars with
  | [] => [[]]
  | c :: chars => if Nat.eqb c 10 then [] :: text_lines chars else
      match text_lines chars with [] => [[c]] | first :: rest => (c :: first) :: rest end
  end.
Fixpoint join_lines lines :=
  match lines with [] => [] | first :: [] => first | first :: rest => first ++ 10 :: join_lines rest end.
Lemma text_lines_nonempty chars : text_lines chars <> [].
Proof. destruct chars; cbn [text_lines]; [discriminate |]. destruct (Nat.eqb n 10); [discriminate |]. destruct (text_lines chars); discriminate. Qed.
Lemma join_text_lines chars : join_lines (text_lines chars) = chars.
Proof.
  induction chars; cbn [text_lines]; [reflexivity |].
  destruct (text_lines chars) as [|row rows] eqn:Lines; [exfalso; now apply (text_lines_nonempty chars) |].
  destruct (Nat.eqb a 10) eqn:Newline.
  - apply Nat.eqb_eq in Newline. subst a. change (10 :: join_lines (row :: rows) = 10 :: chars). now f_equal.
  - destruct rows as [|next tail].
    + change (a :: row = a :: chars). now f_equal.
    + change (a :: (row ++ 10 :: join_lines (next :: tail)) = a :: chars). now f_equal.
Qed.
Definition lex_line chars :=
  let '(spaces, rest) := span (Nat.eqb 32) chars in
  let? tokens := lex (length rest) rest in
  match tokens with [] => Some None | _ => Some (Some (SourceLine (length spaces) tokens)) end.
Fixpoint lex_lines lines : option (list source_line) :=
  match lines with
  | [] => Some []
  | row :: lines =>
      let? first := lex_line row in
      let? rest := lex_lines lines in
      match first with None => Some rest | Some first => Some (first :: rest) end
  end.
Inductive line_lexes : list nat -> option source_line -> Prop :=
| line_lexed spaces rest tokens : Forall (fun c => c = 32) spaces ->
    (rest = [] \/ exists c tail, rest = c :: tail /\ c <> 32) -> lexes rest tokens ->
    line_lexes (spaces ++ rest)
      (match tokens with [] => None | _ => Some (SourceLine (length spaces) tokens) end).
Inductive lines_lexed : list (list nat) -> list source_line -> Prop :=
| lines_empty : lines_lexed [] []
| lines_blank raw rest rows : line_lexes raw None -> lines_lexed rest rows -> lines_lexed (raw :: rest) rows
| lines_code raw row rest rows : line_lexes raw (Some row) -> lines_lexed rest rows ->
    lines_lexed (raw :: rest) (row :: rows).
Theorem lex_line_sound chars row : lex_line chars = Some row -> line_lexes chars row.
Proof.
  unfold lex_line. destruct (span (Nat.eqb 32) chars) as [spaces rest] eqn:Span.
  destruct (lex (length rest) rest) eqn:Lex; try discriminate.
  intro E. destruct (span_sound (Nat.eqb 32) chars spaces rest Span) as [Shape [All End]].
  assert (Valid : line_lexes chars (match l with [] => None | _ => Some (SourceLine (length spaces) l) end)).
  { rewrite Shape. constructor.
    - eapply Forall_impl; [|exact All]. intros c H. now apply Nat.eqb_eq in H.
    - destruct End as [End | [c [tail [End Bad]]]]; auto. right. exists c, tail. split; auto. apply Nat.eqb_neq in Bad. congruence.
    - now apply (lex_sound (length rest)). }
  destruct l; inversion E; subst; exact Valid.
Qed.
Theorem lex_lines_sound lines rows : lex_lines lines = Some rows -> lines_lexed lines rows.
Proof.
  revert rows. induction lines; intros rows E; cbn [lex_lines] in E.
  - inversion E; constructor.
  - destruct (lex_line a) as [[row|]|] eqn:L; try discriminate;
      destruct (lex_lines lines) eqn:Rest; inversion E; subst;
      [eapply lines_code | eapply lines_blank]; eauto using lex_line_sound.
Qed.
Definition tokens_eqb xs ys := if list_eq_dec token_eq_dec xs ys then true else false.
Lemma tokens_eqb_spec xs ys : tokens_eqb xs ys = true <-> xs = ys.
Proof. unfold tokens_eqb. destruct (list_eq_dec token_eq_dec xs ys); intuition discriminate. Qed.
Definition check_expression_end locals functions cert tokens tail :=
  let? (e, rest) := check_expression locals functions 0 cert tokens in
  if tokens_eqb rest tail then Some e else None.
Lemma check_expression_end_sound locals functions cert tokens tail e :
  check_expression_end locals functions cert tokens tail = Some e ->
  parses_expression locals functions 0 tokens e tail.
Proof.
  unfold check_expression_end. destruct (check_expression locals functions 0 cert tokens) as [[value rest]|] eqn:E; try discriminate.
  destruct (tokens_eqb rest tail) eqn:End; try discriminate. apply tokens_eqb_spec in End.
  intro H. inversion H; subst. now apply check_expression_sound in E.
Qed.
Inductive statement_certificate :=
| CertificateEnd | CertificateThen (first rest : statement_certificate)
| CertificatePass | CertificateAssign (n : name) (e : expression_certificate)
| CertificateReturn (e : expression_certificate) | CertificateDiscard (e : expression_certificate)
| CertificateStore (a b : expression_certificate) | CertificateReset (e : expression_certificate)
| CertificateIfThen (e : expression_certificate) (yes : statement_certificate)
| CertificateIf (e : expression_certificate) (yes no : statement_certificate)
| CertificateWhile (e : expression_certificate) (body : statement_certificate).
Fixpoint declarations cert :=
  match cert with
  | CertificateAssign n _ => [n]
  | CertificateThen a b | CertificateIf _ a b => declarations a ++ declarations b
  | CertificateWhile _ b | CertificateIfThen _ b => declarations b
  | _ => [] end.
Definition block_end indent rows := match rows with [] => true | row :: _ => indentation row <? indent end.
Definition nonempty_block cert := match cert with CertificateThen _ _ => true | _ => false end.
Definition nested_indent indent rows :=
  match rows with row :: _ => if indent <? indentation row then Some (indentation row) else None | [] => None end.
Definition keyword_if : name := [105;102].
Definition keyword_else : name := [101;108;115;101].
Definition keyword_while : name := [119;104;105;108;101].
Definition keyword_return : name := [114;101;116;117;114;110].
Definition keyword_pass : name := [112;97;115;115].
Fixpoint check_statement locals functions indent cert rows : option (statement * list source_line) :=
  match rows with
  | [] => None
  | row :: rows =>
      if Nat.eqb (indentation row) indent then
        let tokens := line_tokens row in
        match cert with
        | CertificatePass => if tokens_eqb tokens [Name keyword_pass] then Some (Skip, rows) else None
        | CertificateAssign n e =>
            if valid_name n then
              let? slot := name_index n locals in
              let? tokens := consume (Name n) tokens in
              let? tokens := consume (Symbol [61]) tokens in
              let? e := check_expression_end locals functions e tokens [] in Some (Assign slot e, rows)
            else None
        | CertificateReturn e =>
            let? tokens := consume (Name keyword_return) tokens in
            let? e := check_expression_end locals functions e tokens [] in Some (Return e, rows)
        | CertificateDiscard e =>
            let? e := check_expression_end locals functions e tokens [] in Some (Discard e, rows)
        | CertificateStore a b =>
            let? tokens := consume (Name keyword_store) tokens in
            let? tokens := consume (Symbol [40]) tokens in
            let? (a, tokens) := check_expression locals functions 0 a tokens in
            let? tokens := consume (Symbol [44]) tokens in
            let? b := check_expression_end locals functions b tokens [Symbol [41]] in Some (Write a b, rows)
        | CertificateReset e =>
            let? tokens := consume (Name keyword_reset) tokens in
            let? tokens := consume (Symbol [40]) tokens in
            let? e := check_expression_end locals functions e tokens [Symbol [41]] in Some (Rewind e, rows)
        | CertificateIfThen e yes =>
            if nonempty_block yes then
              let? tokens := consume (Name keyword_if) tokens in
              let? e := check_expression_end locals functions e tokens [Symbol [58]] in
              let? inner := nested_indent indent rows in
              let? (a, rows) := check_block locals functions inner yes rows in
              Some (Conditional e a Skip, rows)
            else None
        | CertificateIf e yes no =>
            if nonempty_block yes && nonempty_block no then
              let? tokens := consume (Name keyword_if) tokens in
              let? e := check_expression_end locals functions e tokens [Symbol [58]] in
              let? inner := nested_indent indent rows in
              let? (a, rows) := check_block locals functions inner yes rows in
              match rows with
              | row :: rows =>
                  if Nat.eqb (indentation row) indent && tokens_eqb (line_tokens row) [Name keyword_else;Symbol [58]] then
                    let? inner := nested_indent indent rows in
                    let? (b, rows) := check_block locals functions inner no rows in Some (Conditional e a b, rows)
                  else None
              | [] => None end
            else None
        | CertificateWhile e body =>
            if nonempty_block body then
              let? tokens := consume (Name keyword_while) tokens in
              let? e := check_expression_end locals functions e tokens [Symbol [58]] in
              let? inner := nested_indent indent rows in
              let? (body, rows) := check_block locals functions inner body rows in Some (While e body, rows)
            else None
        | _ => None end
      else None end
with check_block locals functions indent cert rows : option (statement * list source_line) :=
  match cert with
  | CertificateEnd => if block_end indent rows then Some (Skip, rows) else None
  | CertificateThen first rest =>
      let? (a, rows) := check_statement locals functions indent first rows in
      let? (b, rows) := check_block locals functions indent rest rows in Some (Sequence a b, rows)
  | _ => None end.
Inductive parses_statement locals functions : nat -> list source_line -> statement -> list name -> list source_line -> Prop :=
| parses_pass indent rows : parses_statement locals functions indent
    (SourceLine indent [Name keyword_pass] :: rows) Skip [] rows
| parses_assign indent n slot tokens e rows : valid_name n = true -> name_index n locals = Some slot ->
    parses_expression locals functions 0 tokens e [] ->
    parses_statement locals functions indent (SourceLine indent (Name n :: Symbol [61] :: tokens) :: rows) (Assign slot e) [n] rows
| parses_return indent tokens e rows : parses_expression locals functions 0 tokens e [] ->
    parses_statement locals functions indent (SourceLine indent (Name keyword_return :: tokens) :: rows) (Return e) [] rows
| parses_discard indent tokens e rows : parses_expression locals functions 0 tokens e [] ->
    parses_statement locals functions indent (SourceLine indent tokens :: rows) (Discard e) [] rows
| parses_store indent tokens a middle b rows :
    parses_expression locals functions 0 tokens a (Symbol [44] :: middle) ->
    parses_expression locals functions 0 middle b [Symbol [41]] ->
    parses_statement locals functions indent
      (SourceLine indent (Name keyword_store :: Symbol [40] :: tokens) :: rows) (Write a b) [] rows
| parses_reset indent tokens e rows : parses_expression locals functions 0 tokens e [Symbol [41]] ->
    parses_statement locals functions indent
      (SourceLine indent (Name keyword_reset :: Symbol [40] :: tokens) :: rows) (Rewind e) [] rows
| parses_if_then indent tokens e rows inner a names rest : indent < inner ->
    parses_expression locals functions 0 tokens e [Symbol [58]] ->
    parses_block locals functions inner rows a names rest ->
    parses_statement locals functions indent (SourceLine indent (Name keyword_if :: tokens) :: rows) (Conditional e a Skip) names rest
| parses_if indent tokens e rows yes_indent no_indent a b yes_names no_names rest middle :
    indent < yes_indent -> indent < no_indent ->
    parses_expression locals functions 0 tokens e [Symbol [58]] ->
    parses_block locals functions yes_indent rows a yes_names
      (SourceLine indent [Name keyword_else;Symbol [58]] :: middle) ->
    parses_block locals functions no_indent middle b no_names rest ->
    parses_statement locals functions indent (SourceLine indent (Name keyword_if :: tokens) :: rows)
      (Conditional e a b) (yes_names ++ no_names) rest
| parses_while indent tokens e rows inner body names rest : indent < inner ->
    parses_expression locals functions 0 tokens e [Symbol [58]] ->
    parses_block locals functions inner rows body names rest ->
    parses_statement locals functions indent (SourceLine indent (Name keyword_while :: tokens) :: rows) (While e body) names rest
with parses_block locals functions : nat -> list source_line -> statement -> list name -> list source_line -> Prop :=
| parses_end indent rows : block_end indent rows = true -> parses_block locals functions indent rows Skip [] rows
| parses_then indent rows a a_names middle b b_names rest :
    parses_statement locals functions indent rows a a_names middle ->
    parses_block locals functions indent middle b b_names rest ->
    parses_block locals functions indent rows (Sequence a b) (a_names ++ b_names) rest.
Lemma nested_indent_sound indent rows inner : nested_indent indent rows = Some inner -> indent < inner.
Proof.
  destruct rows; cbn [nested_indent]; try discriminate.
  destruct (indent <? indentation s) eqn:L; try discriminate.
  intro E. inversion E; subst. now apply Nat.ltb_lt in L.
Qed.
Local Ltac statement_header E rows indent :=
  destruct rows as [|[depth tokens] rows]; cbn [check_statement indentation line_tokens] in E; try discriminate;
  destruct (Nat.eqb depth indent) eqn:Depth; try discriminate; apply Nat.eqb_eq in Depth; subst depth.
Theorem check_statements_sound locals functions cert :
  (forall indent rows stmt rest, check_statement locals functions indent cert rows = Some (stmt, rest) ->
    parses_statement locals functions indent rows stmt (declarations cert) rest) /\
  (forall indent rows stmt rest, check_block locals functions indent cert rows = Some (stmt, rest) ->
    parses_block locals functions indent rows stmt (declarations cert) rest).
Proof.
  induction cert.
  - split; intros indent rows stmt rest E.
    + statement_header E rows indent.
    + cbn [check_block] in E. destruct (block_end indent rows) eqn:End; try discriminate.
      inversion E; subst. now constructor.
  - destruct IHcert1 as [First _]. destruct IHcert2 as [_ Tail]. split; intros indent rows stmt rest E.
    + statement_header E rows indent.
    + cbn [check_block] in E.
      destruct (check_statement locals functions indent cert1 rows) as [[a middle]|] eqn:A; try discriminate.
      destruct (check_block locals functions indent cert2 middle) as [[b after]|] eqn:B; try discriminate.
      inversion E; subst. eapply parses_then; eauto.
  - split; intros indent rows stmt rest E; [statement_header E rows indent | discriminate].
    destruct (tokens_eqb tokens [Name keyword_pass]) eqn:T; try discriminate.
    apply tokens_eqb_spec in T. subst tokens. inversion E; subst. constructor.
  - split; intros indent rows stmt rest E; [statement_header E rows indent | discriminate].
    destruct (valid_name n) eqn:V; try discriminate. destruct (name_index n locals) eqn:I; try discriminate.
    destruct (consume (Name n) tokens) eqn:Head; try discriminate.
    destruct (consume (Symbol [61]) l) eqn:Equals; try discriminate.
    destruct (check_expression_end locals functions e l0 []) eqn:Value; try discriminate.
    inversion E; subst. apply consume_sound in Head, Equals. subst tokens l.
    constructor; auto. now apply check_expression_end_sound in Value.
  - split; intros indent rows stmt rest E; [statement_header E rows indent | discriminate].
    destruct (consume (Name keyword_return) tokens) eqn:Head; try discriminate.
    destruct (check_expression_end locals functions e l []) eqn:Value; try discriminate.
    inversion E; subst. apply consume_sound in Head. subst tokens. constructor. now apply check_expression_end_sound in Value.
  - split; intros indent rows stmt rest E; [statement_header E rows indent | discriminate].
    destruct (check_expression_end locals functions e tokens []) eqn:Value; try discriminate.
    inversion E; subst. constructor. now apply check_expression_end_sound in Value.
  - split; intros indent rows stmt rest E; [statement_header E rows indent | discriminate].
    destruct (consume (Name keyword_store) tokens) eqn:Head; try discriminate.
    destruct (consume (Symbol [40]) l) eqn:Open; try discriminate.
    destruct (check_expression locals functions 0 a l0) as [[address middle]|] eqn:A; try discriminate.
    destruct (consume (Symbol [44]) middle) eqn:Comma; try discriminate.
    destruct (check_expression_end locals functions b l1 [Symbol [41]]) eqn:B; try discriminate.
    inversion E; subst. apply consume_sound in Head, Open, Comma. subst tokens l middle.
    eapply parses_store; eauto using check_expression_sound, check_expression_end_sound.
  - split; intros indent rows stmt rest E; [statement_header E rows indent | discriminate].
    destruct (consume (Name keyword_reset) tokens) eqn:Head; try discriminate.
    destruct (consume (Symbol [40]) l) eqn:Open; try discriminate.
    destruct (check_expression_end locals functions e l0 [Symbol [41]]) eqn:Value; try discriminate.
    inversion E; subst. apply consume_sound in Head, Open. subst tokens l.
    constructor. now apply check_expression_end_sound in Value.
  - destruct IHcert as [_ Body]. split; intros indent rows stmt rest E; [statement_header E rows indent | discriminate].
    destruct (nonempty_block cert) eqn:Nonempty; try discriminate.
    destruct (consume (Name keyword_if) tokens) eqn:Head; try discriminate.
    destruct (check_expression_end locals functions e l [Symbol [58]]) eqn:Value; try discriminate.
    destruct (nested_indent indent rows) eqn:Inner; try discriminate.
    destruct (check_block locals functions n cert rows) as [[a after]|] eqn:A; try discriminate.
    inversion E; subst. apply consume_sound in Head. subst tokens.
    cbn [declarations]. eapply parses_if_then with (inner := n); eauto using nested_indent_sound, check_expression_end_sound.
  - destruct IHcert1 as [_ Yes]. destruct IHcert2 as [_ No].
    split; intros indent rows stmt rest E; [statement_header E rows indent | discriminate].
    destruct (nonempty_block cert1 && nonempty_block cert2) eqn:Nonempty; try discriminate.
    destruct (consume (Name keyword_if) tokens) eqn:Head; try discriminate.
    destruct (check_expression_end locals functions e l [Symbol [58]]) eqn:Value; try discriminate.
    destruct (nested_indent indent rows) eqn:Inner; try discriminate.
    destruct (check_block locals functions n cert1 rows) as [[a middle]|] eqn:A; try discriminate.
    destruct middle as [|[depth else_tokens] middle]; try discriminate.
    cbn [indentation line_tokens] in E.
    destruct (Nat.eqb depth indent && tokens_eqb else_tokens [Name keyword_else;Symbol [58]]) eqn:Else; try discriminate.
    apply andb_true_iff in Else. destruct Else as [Depth Else]. apply Nat.eqb_eq in Depth. apply tokens_eqb_spec in Else. subst depth else_tokens.
    destruct (nested_indent indent middle) eqn:NoInner; try discriminate.
    destruct (check_block locals functions n0 cert2 middle) as [[b after]|] eqn:B; try discriminate.
    inversion E; subst. apply consume_sound in Head. subst tokens.
    cbn [declarations]. eapply parses_if with (yes_indent := n) (no_indent := n0); eauto using nested_indent_sound, check_expression_end_sound.
  - destruct IHcert as [_ Body]. split; intros indent rows stmt rest E; [statement_header E rows indent | discriminate].
    destruct (nonempty_block cert) eqn:Nonempty; try discriminate.
    destruct (consume (Name keyword_while) tokens) eqn:Head; try discriminate.
    destruct (check_expression_end locals functions e l [Symbol [58]]) eqn:Value; try discriminate.
    destruct (nested_indent indent rows) eqn:Inner; try discriminate.
    destruct (check_block locals functions n cert rows) as [[a after]|] eqn:A; try discriminate.
    inversion E; subst. apply consume_sound in Head. subst tokens.
    cbn [declarations]. eapply parses_while with (inner := n); eauto using nested_indent_sound, check_expression_end_sound.
Qed.
Definition name_eq_dec := list_eq_dec Nat.eq_dec.
Definition keyword_def : name := [100;101;102].
Definition builtin_name n := existsb (name_eqb n)
  [keyword_load;keyword_alloc;keyword_store;keyword_mark;keyword_reset].
Record function_certificate := FunctionCertificate {
  function_name : name;
  function_parameter : option name;
  function_statements : statement_certificate
}.
Definition parameter_names (p : option name) := match p with None => [] | Some n => [n] end.
Definition add_name names n := if existsb (name_eqb n) names then names else names ++ [n].
Definition local_names parameter assigned := fold_left add_name assigned (parameter_names parameter).
Definition function_header n parameter :=
  [Name keyword_def;Name n;Symbol [40]] ++
  (match parameter with None => [] | Some p => [Name p] end) ++ [Symbol [41];Symbol [58]].
Definition valid_function_name n := valid_name n && negb (builtin_name n).
Definition valid_parameter n parameter :=
  if name_eqb n keyword_main then match parameter with None => true | _ => false end
  else match parameter with Some p => valid_name p | None => false end.
Definition check_function functions cert rows :=
  let n := function_name cert in
  let parameter := function_parameter cert in
  let body := function_statements cert in
  if valid_function_name n && valid_parameter n parameter && nonempty_block body then
    match rows with
    | SourceLine 0 tokens :: rows =>
        if tokens_eqb tokens (function_header n parameter) then
          let? inner := nested_indent 0 rows in
          let? (stmt, rows) := check_block
            (local_names parameter (declarations body)) functions inner body rows in
          Some ((n, Sequence stmt (Return (Literal 0))), rows)
        else None
    | _ => None end
  else None.
Fixpoint check_functions functions certs rows :=
  match certs with
  | [] => match rows with [] => Some [] | _ => None end
  | cert :: certs =>
      let? (f, rows) := check_function functions cert rows in
      let? fs := check_functions functions certs rows in Some (f :: fs)
  end.
Inductive parses_function functions : list source_line -> name * statement -> list source_line -> Prop :=
| parses_definition n parameter inner rows stmt assigned rest :
    valid_function_name n = true -> valid_parameter n parameter = true -> 0 < inner ->
    parses_block (local_names parameter assigned) functions inner rows stmt assigned rest ->
    parses_function functions (SourceLine 0 (function_header n parameter) :: rows)
      (n, Sequence stmt (Return (Literal 0))) rest.
Inductive parses_functions functions : list source_line -> list (name * statement) -> Prop :=
| parses_functions_end : parses_functions functions [] []
| parses_functions_cons rows f middle fs : parses_function functions rows f middle ->
    parses_functions functions middle fs -> parses_functions functions rows (f :: fs).
Lemma check_function_sound functions cert rows f rest :
  check_function functions cert rows = Some (f, rest) -> parses_function functions rows f rest.
Proof.
  destruct cert as [n parameter body]. unfold check_function; cbn [function_name function_parameter function_statements].
  destruct (valid_function_name n && valid_parameter n parameter && nonempty_block body) eqn:Valid; try discriminate.
  rewrite !andb_true_iff in Valid. destruct Valid as [[NameValid ParamValid] Nonempty].
  destruct rows as [|[indent tokens] rows]; try discriminate. destruct indent; try discriminate.
  destruct (tokens_eqb tokens (function_header n parameter)) eqn:Header; try discriminate.
  apply tokens_eqb_spec in Header. subst tokens.
  destruct (nested_indent 0 rows) eqn:Indent; try discriminate.
  destruct (check_block (local_names parameter (declarations body)) functions n0 body rows) as [[stmt after]|] eqn:Body; try discriminate.
  intro E. inversion E; subst. eapply parses_definition with (inner := n0); eauto using nested_indent_sound.
  exact (proj2 (check_statements_sound _ _ body) _ _ _ _ Body).
Qed.
Lemma check_functions_sound functions certs rows fs :
  check_functions functions certs rows = Some fs -> parses_functions functions rows fs.
Proof.
  revert rows fs. induction certs; intros rows fs E; cbn [check_functions] in E.
  - destruct rows; inversion E; constructor.
  - destruct (check_function functions a rows) as [[f middle]|] eqn:F; try discriminate.
    destruct (check_functions functions certs middle) eqn:Fs; try discriminate.
    inversion E; subst. econstructor; eauto using check_function_sound.
Qed.
Definition ordered_names certs := keyword_main :: filter (fun n => negb (name_eqb n keyword_main)) (map function_name certs).
Definition unique_function_names certs :=
  Nat.eqb (length (nodup name_eq_dec (map function_name certs))) (length certs) &&
  existsb (fun cert => name_eqb (function_name cert) keyword_main) certs.
Definition order_functions (fs : list (name * statement)) :=
  match find (fun f => name_eqb (fst f) keyword_main) fs with
  | Some main => Some (snd main :: map snd (filter (fun f => negb (name_eqb (fst f) keyword_main)) fs))
  | None => None end.
Definition check_frontend chars certs :=
  if unique_function_names certs then
    let? rows := lex_lines (text_lines chars) in
    let? fs := check_functions (ordered_names certs) certs rows in
    order_functions fs
  else None.
Inductive parses_program : list nat -> list statement -> Prop :=
| parses_source chars lines rows named functions fs :
    join_lines lines = chars -> lines_lexed lines rows ->
    NoDup (map fst named) -> functions = keyword_main :: filter (fun n => negb (name_eqb n keyword_main)) (map fst named) ->
    parses_functions functions rows named -> order_functions named = Some fs ->
    parses_program chars fs.
Lemma checked_function_name functions cert rows f rest :
  check_function functions cert rows = Some (f, rest) -> fst f = function_name cert.
Proof.
  destruct cert as [n parameter body]. unfold check_function; cbn [function_name function_parameter function_statements].
  destruct (valid_function_name n && valid_parameter n parameter && nonempty_block body); try discriminate.
  destruct rows as [|[indent tokens] rows]; try discriminate. destruct indent; try discriminate.
  destruct (tokens_eqb tokens (function_header n parameter)); try discriminate.
  destruct (nested_indent 0 rows); try discriminate.
  destruct (check_block (local_names parameter (declarations body)) functions n0 body rows) as [[stmt after]|]; try discriminate.
  intro E. inversion E. reflexivity.
Qed.
Lemma checked_function_names functions certs rows fs :
  check_functions functions certs rows = Some fs -> map fst fs = map function_name certs.
Proof.
  revert rows fs. induction certs; intros rows fs E; cbn [check_functions] in E.
  - destruct rows; inversion E. reflexivity.
  - destruct (check_function functions a rows) as [[f middle]|] eqn:F; try discriminate.
    destruct (check_functions functions certs middle) eqn:Fs; try discriminate.
    inversion E; subst. cbn. rewrite (checked_function_name _ _ _ _ _ F). f_equal. eauto.
Qed.
Lemma nodup_length_bound (xs : list name) : length (nodup name_eq_dec xs) <= length xs.
Proof.
  induction xs; cbn; auto. destruct (in_dec name_eq_dec a xs); cbn; lia.
Qed.
Lemma nodup_length_unique (xs : list name) : length (nodup name_eq_dec xs) = length xs -> NoDup xs.
Proof.
  induction xs; cbn; intro E; [constructor |].
  destruct (in_dec name_eq_dec a xs) as [Present|Absent].
  - pose proof (nodup_length_bound xs). lia.
  - cbn in E. constructor; auto.
Qed.
Theorem check_frontend_sound chars certs fs : check_frontend chars certs = Some fs -> parses_program chars fs.
Proof.
  unfold check_frontend. destruct (unique_function_names certs) eqn:Unique; try discriminate.
  destruct (lex_lines (text_lines chars)) eqn:Lex; try discriminate.
  destruct (check_functions (ordered_names certs) certs l) eqn:Functions; try discriminate.
  intro Order. eapply parses_source with (lines := text_lines chars) (rows := l) (named := l0) (functions := ordered_names certs).
  - apply join_text_lines.
  - now apply lex_lines_sound.
  - pose proof (checked_function_names _ _ _ _ Functions) as Names. rewrite Names.
    unfold unique_function_names in Unique. apply andb_true_iff in Unique. destruct Unique as [Unique _].
    apply Nat.eqb_eq in Unique. rewrite <- (length_map function_name certs) in Unique.
    apply nodup_length_unique. exact Unique.
  - unfold ordered_names. now rewrite (checked_function_names _ _ _ _ Functions).
  - now apply check_functions_sound in Functions.
  - exact Order.
Qed.

Definition compile_text chars certs :=
  let? fs := check_frontend chars certs in compile_bytes fs.
Theorem compile_text_sound chars certs code : compile_text chars certs = Some code ->
  exists fs, parses_program chars fs /\ compile_bytes fs = Some code.
Proof.
  unfold compile_text. destruct (check_frontend chars certs) eqn:Parsed; try discriminate.
  intro Compiled. exists l. split; [exact (check_frontend_sound _ _ _ Parsed) | exact Compiled].
Qed.
Theorem compile_text_bytes chars certs code : compile_text chars certs = Some code ->
  Forall (fun b => b < 256) code /\ Verifier.verify code = true.
Proof.
  intro C. destruct (compile_text_sound _ _ _ C) as [fs [_ Compiled]].
  destruct (compile_bytes_checked _ _ Compiled) as [Checked Bytes].
  split; [exact Bytes | exact (compilation_verified _ _ Checked)].
Qed.
