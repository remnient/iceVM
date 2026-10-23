#ifndef ICEVM_H
#define ICEVM_H
#include <stddef.h>
#include <stdint.h>

#define ICEVM_MEMORY 65536
#define ICEVM_STACK 256

enum icevm_status { ICEVM_RUNNING, ICEVM_STOPPED, ICEVM_FAULT };
enum icevm_fault { ICEVM_EXPLICIT, ICEVM_DECODE, ICEVM_TARGET, ICEVM_MEM,
                 ICEVM_REGION, ICEVM_STACK_FAULT, ICEVM_DIVISION };
struct icevm_frame { uint64_t pc, regs[16]; };
struct icevm {
  uint64_t pc, regs[16];
  uint8_t memory[ICEVM_MEMORY];
  size_t frontier, depth;
  struct icevm_frame stack[ICEVM_STACK];
  enum icevm_status status;
  enum icevm_fault fault;
};
struct icevm_code {
  const uint8_t *bytes;
  size_t size;
  uint8_t *boundary;
  size_t *owner;
};
struct icevm_instruction { unsigned op, d, a, b, width; uint64_t imm; };
int icevm_decode(const struct icevm_code *, uint64_t, struct icevm_instruction *);
int icevm_code_init(struct icevm_code *, const uint8_t *, size_t);
void icevm_code_destroy(struct icevm_code *);
int icevm_verify(const struct icevm_code *, uint64_t *);
void icevm_step(struct icevm *, const struct icevm_code *);
#endif
