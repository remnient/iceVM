open Model

type sexp = Atom of string | List of sexp list

let parse text =
  let tokens = String.split_on_char ' ' (String.concat " ( " (String.split_on_char '(' text)) in
  let tokens = String.concat " " tokens |> String.split_on_char ')' |> String.concat " ) "
    |> String.split_on_char ' ' |> List.filter (fun s -> s <> "") in
  let rec item = function
    | "(" :: rest -> items [] rest
    | x :: rest -> Atom x, rest
    | [] -> failwith "unexpected end"
  and items acc = function
    | ")" :: rest -> List (List.rev acc), rest
    | [] -> failwith "unclosed list"
    | tokens -> let x, rest = item tokens in items (x :: acc) rest
  in
  match item tokens with x, [] -> x | _ -> failwith "trailing tokens"

let number = function
  | Atom x -> let n = Z.of_string x in
      if Z.sign n < 0 then failwith "expected natural number" else n
  | _ -> failwith "expected number"
let op = function
  | "add" -> Add | "sub" -> Sub | "mul" -> Mul | "div" -> Div
  | "and" -> And | "or" -> Or | "xor" -> Xor | "shl" -> Shl | "shr" -> Shr
  | "eq" -> Eq0 | "lt" -> Lt0 | _ -> failwith "unknown operator"

let comparison = function
  | "eq" -> CSame | "ne" -> CDifferent | "lt" -> CBelow
  | "le" -> CAtMost | "gt" -> CAbove | "ge" -> CAtLeast
  | _ -> failwith "unknown comparison"

let rec expression = function
  | List [Atom "lit"; n] -> Literal (number n)
  | List [Atom "var"; n] -> Local (number n)
  | List [Atom "bin"; Atom f; a; b] -> Operation (op f, expression a, expression b)
  | List [Atom "cmp"; Atom op; a; b] -> Compare (comparison op, expression a, expression b)
  | List [Atom "load"; a] -> Read (expression a)
  | List [Atom "alloc"; a] -> New (expression a)
  | List [Atom "call"; f; a] -> Invoke (number f, expression a)
  | List [Atom "mark"] -> Watermark
  | _ -> failwith "invalid expression"

let rec statement = function
  | List [Atom "skip"] -> Skip
  | List [Atom "set"; n; e] -> Assign (number n, expression e)
  | List [Atom "discard"; e] -> Discard (expression e)
  | List [Atom "store"; a; v] -> Write (expression a, expression v)
  | List [Atom "reset"; e] -> Rewind (expression e)
  | List [Atom "seq"; a; b] -> Sequence (statement a, statement b)
  | List [Atom "if"; e; a; b] -> Conditional (expression e, statement a, statement b)
  | List [Atom "while"; e; a] -> While (expression e, statement a)
  | List [Atom "return"; e] -> Return (expression e)
  | _ -> failwith "invalid statement"

let functions text = match parse text with
  | List xs -> List.map statement xs
  | _ -> failwith "invalid program"

let program text =
  let functions = Array.of_list (functions text) in
  let lookup n = if Z.sign n < 0 || Z.compare n (Z.of_int (Array.length functions)) >= 0
    then None else Some functions.(Z.to_int n) in
  lookup, functions.(0)

let name = function List xs -> List.map number xs | _ -> failwith "invalid name"

let rec expression_certificate = function
  | List [Atom "literal"; n] -> CertificateLiteral (number n)
  | List [Atom "boolean"; Atom b] -> CertificateBoolean (match b with
      | "true" -> true | "false" -> false | _ -> failwith "invalid boolean")
  | List [Atom "name"; n] -> CertificateName (name n)
  | List [Atom "binary"; Atom f; a; b] -> CertificateBinary (op f, expression_certificate a, expression_certificate b)
  | List [Atom "comparison"; Atom f; a; b] -> CertificateComparison (comparison f, expression_certificate a, expression_certificate b)
  | List [Atom "unary"; Atom u; e] -> CertificateUnary ((match u with
      | "neg" -> Negative | "invert" -> Complement | "not" -> LogicalNot
      | _ -> failwith "invalid unary operator"), expression_certificate e)
  | List [Atom "paren"; e] -> CertificateParenthesis (expression_certificate e)
  | List [Atom "call0"; n] -> CertificateCallZero (name n)
  | List [Atom "call1"; n; e] -> CertificateCallOne (name n, expression_certificate e)
  | _ -> failwith "invalid expression certificate"

let rec statement_certificate = function
  | List [Atom "end"] -> CertificateEnd
  | List [Atom "then"; a; b] -> CertificateThen (statement_certificate a, statement_certificate b)
  | List [Atom "pass"] -> CertificatePass
  | List [Atom "assign"; n; e] -> CertificateAssign (name n, expression_certificate e)
  | List [Atom "return"; e] -> CertificateReturn (expression_certificate e)
  | List [Atom "discard"; e] -> CertificateDiscard (expression_certificate e)
  | List [Atom "store"; a; b] -> CertificateStore (expression_certificate a, expression_certificate b)
  | List [Atom "reset"; e] -> CertificateReset (expression_certificate e)
  | List [Atom "ifthen"; e; a] -> CertificateIfThen (expression_certificate e, statement_certificate a)
  | List [Atom "if"; e; a; b] -> CertificateIf (expression_certificate e, statement_certificate a, statement_certificate b)
  | List [Atom "while"; e; a] -> CertificateWhile (expression_certificate e, statement_certificate a)
  | _ -> failwith "invalid statement certificate"

let certificate text = match parse text with
  | List fs -> List.map (function
      | List [n; parameter; body] -> {
          function_name = name n;
          function_parameter = (match parameter with List [Atom "none"] -> None
            | List [Atom "some"; n] -> Some (name n) | _ -> failwith "invalid parameter");
          function_statements = statement_certificate body }
      | _ -> failwith "invalid function certificate") fs
  | _ -> failwith "invalid source certificate"
