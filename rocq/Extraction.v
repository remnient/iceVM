From Stdlib Require Import Extraction ExtrOcamlBasic ExtrOcamlNatBigInt ExtrOcamlZBigInt.
From IceVM Require Import Syntax State Semantics Interpreter Verifier Source Compiler Encoding Frontend Optimisation.
Extraction Language OCaml.
Set Extraction Output Directory "build".
Extraction "model.ml" initial step verify source_initial source_step validate_optimisation valid_program emit_program compilation_check compile_bytes compile_text check_frontend.
