#include "../src/vm.h"
#include <stdlib.h>

int main(void) {
  static const uint8_t bytes[] = {2, 27, 8, 11, 0, 0, 0, 0, 0, 0, 0, 0};
  struct icevm_code code;
  struct icevm *state = calloc(1, sizeof *state);
  if (!state) return 2;
  if (!icevm_code_init(&code, bytes, sizeof bytes)) {
    free(state);
    return 2;
  }
  uint64_t bad;
  int verified = icevm_verify(&code, &bad);
  state->pc = 3;
  icevm_step(state, &code);
  int correct = verified && state->status == ICEVM_FAULT && state->fault == ICEVM_TARGET && state->pc == 3;
  icevm_code_destroy(&code);
  free(state);
  return !correct;
}
