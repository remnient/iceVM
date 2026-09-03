CC = cc
CFLAGS = -std=c11 -O2 -Wall -Wextra -Wpedantic -Wconversion -Werror
SOURCE_PATH = /home/james/loosevm
CPPFLAGS = -fmacro-prefix-map=$(CURDIR)=$(SOURCE_PATH)
DEBUGFLAGS = -fdebug-prefix-map=$(CURDIR)=$(SOURCE_PATH)
OPAM_BIN = $(shell opam var bin 2>/dev/null)
ROCQ ?= $(shell if test -x '$(OPAM_BIN)/rocq'; then echo '$(OPAM_BIN)/rocq'; else command -v rocq; fi)
OCAMLFIND ?= $(shell if test -x '$(OPAM_BIN)/ocamlfind'; then echo '$(OPAM_BIN)/ocamlfind'; else command -v ocamlfind; fi)
ROCQLIBS = Syntax State Semantics Interpreter Verifier

.PHONY: all check clean
all: build/loosevm
build/loosevm: src/vm.c src/vm.h src/main.c Makefile
	mkdir -p build
	$(CC) $(CPPFLAGS) $(DEBUGFLAGS) $(CFLAGS) src/vm.c src/main.c -o $@
clean:
	rm -rf build

check: all build/c-interface
	build/c-interface

build/c-interface: src/vm.c src/vm.h tests/c_interface.c Makefile
	$(CC) $(CPPFLAGS) $(DEBUGFLAGS) $(CFLAGS) src/vm.c tests/c_interface.c -o $@

proofs: | build
	@set -e; for f in $(ROCQLIBS); do $(ROCQ) compile -Q rocq Loosevm rocq/$$f.v; done
	@sed -i 's|$(CURDIR)|$(SOURCE_PATH)|g' rocq/.*.aux

build:
	mkdir -p build
