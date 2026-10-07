CC = cc
CFLAGS = -std=c11 -O2 -Wall -Wextra -Wpedantic -Wconversion -Werror
SOURCE_PATH = /home/james/loosevm
CPPFLAGS = -fmacro-prefix-map=$(CURDIR)=$(SOURCE_PATH)
DEBUGFLAGS = -fdebug-prefix-map=$(CURDIR)=$(SOURCE_PATH)
OPAM_BIN = $(shell opam var bin 2>/dev/null)
ROCQ ?= $(shell if test -x '$(OPAM_BIN)/rocq'; then echo '$(OPAM_BIN)/rocq'; else command -v rocq; fi)
OCAMLFIND ?= $(shell if test -x '$(OPAM_BIN)/ocamlfind'; then echo '$(OPAM_BIN)/ocamlfind'; else command -v ocamlfind; fi)
ROCQLIBS = Syntax State Semantics Interpreter Verifier Source Compiler Encoding Frontend Simulation Optimisation TotalSimulation Forward Extraction

.PHONY: all proofs check clean sanitize
all: build/loosevm
build/loosevm: src/vm.c src/vm.h src/main.c Makefile
	mkdir -p build
	$(CC) $(CPPFLAGS) $(DEBUGFLAGS) $(CFLAGS) src/vm.c src/main.c -o $@
proofs: | build
	@set -e; for f in $(ROCQLIBS); do $(ROCQ) compile -Q rocq Loosevm rocq/$$f.v; done
	$(ROCQ) compile -Q rocq Loosevm -Q tests LoosevmTests tests/Proofs.v
	@sed -i 's|$(CURDIR)|$(SOURCE_PATH)|g' rocq/.*.aux tests/.*.aux
check: all build/model build/c-interface
	build/c-interface
	python3 tests/test.py
build/model: proofs tests/model_main.ml tests/source_input.ml
	PATH="$(OPAM_BIN):$$PATH" $(OCAMLFIND) ocamlopt -w -a -ccopt -Wl,--strip-debug -package zarith -linkpkg -I build build/model.mli build/model.ml tests/source_input.ml tests/model_main.ml -I tests -o $@
sanitize: build/model
	$(MAKE) CFLAGS='-std=c11 -O1 -g -Wall -Wextra -Wpedantic -Wconversion -Werror -fsanitize=address,undefined -fno-omit-frame-pointer' build/loosevm-sanitize build/c-interface-sanitize
	ASAN_OPTIONS=detect_leaks=0 UBSAN_OPTIONS=halt_on_error=1 build/c-interface-sanitize
	LOOSEVM=build/loosevm-sanitize ASAN_OPTIONS=detect_leaks=0 UBSAN_OPTIONS=halt_on_error=1 python3 tests/test.py
build/loosevm-sanitize: src/vm.c src/vm.h src/main.c Makefile
	$(CC) $(CPPFLAGS) $(DEBUGFLAGS) $(CFLAGS) src/vm.c src/main.c -o $@
clean:
	rm -rf build tools/__pycache__ tests/__pycache__
	rm -f rocq/*.vo rocq/*.vos rocq/*.vok rocq/*.glob rocq/.*.aux tests/*.cm* tests/*.o tests/*.vo tests/*.vos tests/*.vok tests/*.glob tests/.*.aux .lia.cache .nia.cache

build:
	mkdir -p build


build/c-interface build/c-interface-sanitize: src/vm.c src/vm.h tests/c_interface.c Makefile
	$(CC) $(CPPFLAGS) $(DEBUGFLAGS) $(CFLAGS) src/vm.c tests/c_interface.c -o $@
