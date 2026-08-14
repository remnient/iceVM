#include "vm.h"
#include <errno.h>
#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static void dump(const struct lvm *s) {
  const char *status[] = {"running", "stopped", "fault"};
  printf("{\"status\":\"%s\",\"fault\":%u,\"pc\":%" PRIu64 ",\"frontier\":%zu,\"depth\":%zu,\"regs\":[",
         status[s->status], (unsigned)s->fault, s->pc, s->frontier, s->depth);
  for (unsigned i = 0; i < 16; i++) printf("%s%" PRIu64, i ? "," : "", s->regs[i]);
  printf("],\"memory\":\"");
  for (size_t i = 0; i < LVM_MEMORY; i++) printf("%02x", s->memory[i]);
  printf("\",\"stack\":[");
  for (size_t f = 0; f < s->depth; f++) {
    printf("%s[%" PRIu64, f ? "," : "", s->stack[f].pc);
    for (unsigned i = 0; i < 16; i++) printf(",%" PRIu64, s->stack[f].regs[i]);
    printf("]");
  }
  puts("]}");
}

int main(int argc, char **argv) {
  if (argc < 2 || argc > 5) {
    fprintf(stderr, "usage: loosevm file [fuel] [--raw] [--trace]\n");
    return 2;
  }
  uint64_t fuel = 1000000;
  int raw = 0, trace = 0;
  for (int i = 2; i < argc; i++) {
    if (!strcmp(argv[i], "--raw")) raw = 1;
    else if (!strcmp(argv[i], "--trace")) trace = 1;
    else {
      char *end;
      errno = 0;
      fuel = strtoull(argv[i], &end, 10);
      if (errno || !*argv[i] || *end || argv[i][0] == '-') return 2;
    }
  }
  FILE *f = fopen(argv[1], "rb");
  if (!f) { perror(argv[1]); return 2; }
  if (fseek(f, 0, SEEK_END)) { fclose(f); return 2; }
  long length = ftell(f);
  if (length < 0 || (uintmax_t)length > UINT32_MAX || fseek(f, 0, SEEK_SET)) {
    fclose(f); return 2;
  }
  size_t n = (size_t)length;
  uint8_t *bytes = malloc(n ? n : 1);
  if (!bytes) { fclose(f); return 2; }
  int ok = fread(bytes, 1, n, f) == n;
  if (fclose(f)) ok = 0;
  if (!ok) { free(bytes); return 2; }
  struct lvm_code code;
  if (!lvm_code_init(&code, bytes, n)) { free(bytes); return 2; }
  uint64_t bad;
  if (!raw && !lvm_verify(&code, &bad)) {
    fprintf(stderr, "verification failed at byte %" PRIu64 "\n", bad);
    lvm_code_destroy(&code); free(bytes); return 2;
  }
  struct lvm *s = calloc(1, sizeof *s);
  if (!s) { lvm_code_destroy(&code); free(bytes); return 2; }
  if (trace) dump(s);
  while (fuel && s->status == LVM_RUNNING) {
    fuel--;
    lvm_step(s, &code);
    if (trace) dump(s);
  }
  if (!trace) dump(s);
  int result = s->status == LVM_STOPPED ? 0 : s->status == LVM_FAULT ? 1 : 3;
  if (fflush(stdout) == EOF || ferror(stdout)) result = 2;
  free(s);
  lvm_code_destroy(&code);
  free(bytes);
  return result;
}
