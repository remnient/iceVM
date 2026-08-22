#include "../src/vm.h"
#include <stdlib.h>

int main(void) {
  static const uint8_t bytes[] = {2, 27, 8, 11, 0, 0, 0, 0, 0, 0, 0, 0};
  struct lvm_code code;
  struct lvm *state = calloc(1, sizeof *state);
  if (!state) return 2;
  if (!lvm_code_init(&code, bytes, sizeof bytes)) {
    free(state);
    return 2;
  }
  uint64_t bad;
  int verified = lvm_verify(&code, &bad);
  state->pc = 3;
  lvm_step(state, &code);
  int correct = verified && state->status == LVM_FAULT && state->fault == LVM_TARGET && state->pc == 3;
  lvm_code_destroy(&code);
  free(state);
  return !correct;
}
