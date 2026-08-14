CC = cc
CFLAGS = -std=c11 -O2 -Wall -Wextra -Wpedantic -Wconversion -Werror
SOURCE_PATH = /home/james/loosevm
CPPFLAGS = -fmacro-prefix-map=$(CURDIR)=$(SOURCE_PATH)
DEBUGFLAGS = -fdebug-prefix-map=$(CURDIR)=$(SOURCE_PATH)

.PHONY: all check clean
all: build/loosevm
build/loosevm: src/vm.c src/vm.h src/main.c Makefile
	mkdir -p build
	$(CC) $(CPPFLAGS) $(DEBUGFLAGS) $(CFLAGS) src/vm.c src/main.c -o $@
clean:
	rm -rf build
