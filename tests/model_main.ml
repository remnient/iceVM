open Model

let dump s =
  let status, fault = match s.mode with
    | Running -> "running", 0
    | Stopped -> "stopped", 0
    | Fault Explicit -> "fault", 0
    | Fault Decode -> "fault", 1
    | Fault Target -> "fault", 2
    | Fault Memory -> "fault", 3
    | Fault Region -> "fault", 4
    | Fault Stack -> "fault", 5
    | Fault Division -> "fault", 6
  in
  Printf.printf "{\"status\":\"%s\",\"fault\":%d,\"pc\":%s,\"frontier\":%s,\"depth\":%d,\"regs\":["
    status fault (Z.to_string s.pc) (Z.to_string s.frontier) (List.length s.frames);
  for i = 0 to 15 do
    Printf.printf "%s%s" (if i = 0 then "" else ",") (Z.to_string (s.regs (Z.of_int i)))
  done;
  Printf.printf "],\"memory\":\"";
  for i = 0 to 65535 do Printf.printf "%02x" (Z.to_int (s.mem (Z.of_int i))) done;
  Printf.printf "\",\"stack\":[";
  List.iteri (fun i f ->
    Printf.printf "%s[%s" (if i = 0 then "" else ",") (Z.to_string f.return_pc);
    for j = 0 to 15 do Printf.printf ",%s" (Z.to_string (f.saved (Z.of_int j))) done;
    Printf.printf "]") (List.rev s.frames);
  Printf.printf "]}\n%!"

let binary_name = function
  | Add -> "add" | Sub -> "sub" | Mul -> "mul" | Div -> "div"
  | And -> "and" | Or -> "or" | Xor -> "xor" | Shl -> "shl" | Shr -> "shr"
  | Eq0 -> "eq" | Lt0 -> "lt"

let emit_instruction i =
  let z = Z.to_string in
  let reg r = "r" ^ z r in
  let out op operands = print_endline (op ^ if operands = [] then "" else " " ^ String.concat ", " operands) in
  match i with
  | Halt -> out "halt" [] | Trap -> out "trap" [] | Entry -> out "entry" []
  | Ret -> out "ret" [] | Nop -> out "nop" [] | Pad n -> out "pad" [z (Z.add n (Z.of_int 2))]
  | Imm (d, n) -> out "li" [reg d; z n]
  | Move (d, a) -> out "mov" [reg d; reg a]
  | Binary (op, d, a, b) -> out (binary_name op) [reg d; reg a; reg b]
  | Load (d, a) -> out "load" [reg d; reg a]
  | Store (a, b) -> out "store" [reg a; reg b]
  | Alloc (d, a) -> out "alloc" [reg d; reg a]
  | Mark d -> out "mark" [reg d] | Reset a -> out "reset" [reg a]
  | Jump p -> out "jmp" [z p] | Branch (a, p) -> out "jnz" [reg a; z p]
  | Indirect a -> out "ijmp" [reg a] | Call p -> out "call" [z p]

let bytes data = List.init (String.length data) (fun i -> Z.of_int (Char.code data.[i]))
let read_file path =
  let f = open_in_bin path in
  let data = really_input_string f (in_channel_length f) in
  close_in f;
  data

let source_run data fuel =
  let program, body = Source_input.program data in
  let rec run n s = if n = 0 then s else match source_step program s with
    | None -> s | Some t -> run (n - 1) t in
  let s = run fuel (source_initial body) in
  let result = match s.source_control with Value n | Returning n -> n | _ -> Z.zero in
  let mode, fault = match s.source_mode with
    | Running -> "running", 0 | Stopped -> "stopped", 0
    | Fault f -> "fault", (match f with Explicit -> 0 | Decode -> 1 | Target -> 2
      | Memory -> 3 | Region -> 4 | Stack -> 5 | Division -> 6) in
  Printf.printf "{\"status\":\"%s\",\"fault\":%d,\"result\":%s,\"frontier\":%s,\"memory\":\""
    mode fault (Z.to_string result) (Z.to_string s.source_frontier);
  for i = 0 to 65535 do Printf.printf "%02x" (Z.to_int (s.source_memory (Z.of_int i))) done;
  Printf.printf "\"}\n"

let () =
  let f = open_in_bin Sys.argv.(1) in
  let data = really_input_string f (in_channel_length f) in
  close_in f;
  if Array.length Sys.argv = 4 && Sys.argv.(2) = "--compile-text" then begin
    let certificate = Source_input.certificate (read_file Sys.argv.(3)) in
    match compile_text (bytes data) certificate with
    | Some code -> List.iter (fun byte -> output_char stdout (Char.chr (Z.to_int byte))) code
    | None -> failwith "invalid source or rejected certificate"
  end else if Array.length Sys.argv = 3 && Sys.argv.(2) = "--compile-bytes" then begin
    let functions = Source_input.functions data in
    match compile_bytes functions with
    | Some code -> List.iter (fun byte -> output_char stdout (Char.chr (Z.to_int byte))) code
    | None -> failwith "invalid source or rejected compilation"
  end else if Array.length Sys.argv = 3 && Sys.argv.(2) = "--emit-compiler" then begin
    let functions = Source_input.functions data in
    if not (valid_program functions) then failwith "invalid source program";
    List.iter emit_instruction (emit_program functions)
  end else if Array.length Sys.argv = 4 && Sys.argv.(2) = "--validate-compiler" then begin
    let functions = Source_input.functions data in
    let code = bytes (read_file Sys.argv.(3)) in
    print_endline (if compilation_check functions code then "true" else "false")
  end else if Array.length Sys.argv > 3 && Sys.argv.(3) = "--source" then
    source_run data (int_of_string Sys.argv.(2))
  else begin
  let code = List.init (String.length data) (fun i -> Z.of_int (Char.code data.[i])) in
  if Array.length Sys.argv = 4 && Sys.argv.(2) = "--validate-opt" then begin
    let g = open_in_bin Sys.argv.(3) in
    let other = really_input_string g (in_channel_length g) in
    close_in g;
    let other = List.init (String.length other) (fun i -> Z.of_int (Char.code other.[i])) in
    print_endline (if validate_optimisation code other then "true" else "false")
  end else if Array.length Sys.argv = 3 && Sys.argv.(2) = "--verify" then begin
    print_endline (if verify code then "true" else "false")
  end else begin
    let fuel = int_of_string Sys.argv.(2) in
    let trace = Array.length Sys.argv > 3 && Sys.argv.(3) = "--trace" in
    let rec run n s =
      if trace then dump s;
      if n = 0 then s else match step code s with None -> s | Some t -> run (n - 1) t
    in
    let result = run fuel initial in
    if not trace then dump result
  end
  end
