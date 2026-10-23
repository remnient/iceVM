CC = cc
CFLAGS = -std=c11 -O2 -Wall -Wextra -Wpedantic -Wconversion -Werror
SOURCE_PATH = /home/james/iceVM
CPPFLAGS = -fmacro-prefix-map=$(CURDIR)=$(SOURCE_PATH)
DEBUGFLAGS = -fdebug-prefix-map=$(CURDIR)=$(SOURCE_PATH)
OPAM_BIN = $(shell opam var bin 2>/dev/null)
ROCQ ?= $(shell if test -x '$(OPAM_BIN)/rocq'; then echo '$(OPAM_BIN)/rocq'; else command -v rocq; fi)
OCAMLFIND ?= $(shell if test -x '$(OPAM_BIN)/ocamlfind'; then echo '$(OPAM_BIN)/ocamlfind'; else command -v ocamlfind; fi)
ROCQLIBS = Syntax State Semantics Interpreter Verifier Source Compiler Encoding Frontend Simulation Optimisation TotalSimulation Forward Extraction

.PHONY: all proofs check clean sanitize
all: build/iceVM
build/iceVM: src/vm.c src/vm.h src/main.c Makefile
	mkdir -p build
	$(CC) $(CPPFLAGS) $(DEBUGFLAGS) $(CFLAGS) src/vm.c src/main.c -o $@
proofs: | build
	@set -e; for f in $(ROCQLIBS); do $(ROCQ) compile -Q rocq IceVM rocq/$$f.v; done
	$(ROCQ) compile -Q rocq IceVM -Q tests IceVMTests tests/Proofs.v
	@sed -i 's|$(CURDIR)|$(SOURCE_PATH)|g' rocq/.*.aux tests/.*.aux
check: all build/model build/c-interface
	build/c-interface
	python3 tests/test.py
build/model: proofs tests/model_main.ml tests/source_input.ml
	PATH="$(OPAM_BIN):$$PATH" $(OCAMLFIND) ocamlopt -w -a -ccopt -Wl,--strip-debug -package zarith -linkpkg -I build build/model.mli build/model.ml tests/source_input.ml tests/model_main.ml -I tests -o $@
sanitize: build/model
	$(MAKE) CFLAGS='-std=c11 -O1 -g -Wall -Wextra -Wpedantic -Wconversion -Werror -fsanitize=address,undefined -fno-omit-frame-pointer' build/iceVM-sanitize build/c-interface-sanitize
	ASAN_OPTIONS=detect_leaks=0 UBSAN_OPTIONS=halt_on_error=1 build/c-interface-sanitize
	ICEVM=build/iceVM-sanitize ASAN_OPTIONS=detect_leaks=0 UBSAN_OPTIONS=halt_on_error=1 python3 tests/test.py
build/iceVM-sanitize: src/vm.c src/vm.h src/main.c Makefile
	$(CC) $(CPPFLAGS) $(DEBUGFLAGS) $(CFLAGS) src/vm.c src/main.c -o $@
clean:
	rm -rf build tools/__pycache__ tests/__pycache__
	rm -f rocq/*.vo rocq/*.vos rocq/*.vok rocq/*.glob rocq/.*.aux tests/*.cm* tests/*.o tests/*.vo tests/*.vos tests/*.vok tests/*.glob tests/.*.aux .lia.cache .nia.cache

build:
	mkdir -p build

MENHIR ?= $(shell command -v menhir)
PROOF_CACHE ?= $(HOME)/.cache
COMPCERT ?= $(PROOF_CACHE)/iceVM-compcert-3.18
VST ?= $(PROOF_CACHE)/iceVM-vst-2.17
CROCQFLAGS = -Q rocq IceVM -Q build/cproof IceVMC $(foreach d,lib common x86_64 x86 cfrontend export,-R $(COMPCERT)/$(d) compcert.$(d)) -R $(COMPCERT)/flocq Flocq $(foreach d,msl sepcomp veric zlist floyd,-Q $(VST)/$(d) VST.$(d))
.PHONY: proof-deps cproofs
proof-deps:
	PATH="$(OPAM_BIN):$$PATH" python3 tools/proof_deps.py --cache $(PROOF_CACHE) --rocq $(ROCQ) --menhir $(MENHIR)
build/cproof/CProgram.v: src/vm.c src/vm.h
	mkdir -p build/cproof
	$(COMPCERT)/clightgen -normalize -short-idents -stdlib $(COMPCERT)/runtime -o $@ src/vm.c
cproofs: proofs build/cproof/CProgram.v
	$(ROCQ) compile $(CROCQFLAGS) build/cproof/CProgram.v
	@set -e; for f in CIntegers CRepresentation CState CSpecification CProof CDecoder CStep CMetadata CVerifier CInitialisation; do $(ROCQ) compile $(CROCQFLAGS) rocq/$$f.v; done
	@sed -i 's|$(CURDIR)|$(SOURCE_PATH)|g' build/cproof/.*.aux rocq/.*.aux

build/c-interface build/c-interface-sanitize: src/vm.c src/vm.h tests/c_interface.c Makefile
	$(CC) $(CPPFLAGS) $(DEBUGFLAGS) $(CFLAGS) src/vm.c tests/c_interface.c -o $@
