#ifndef LOOSEVM_H
#define LOOSEVM_H
#include <stddef.h>
#include <stdint.h>

#define LVM_MEMORY 65536
#define LVM_STACK 256

enum lvm_status { LVM_RUNNING, LVM_STOPPED, LVM_FAULT };
enum lvm_fault { LVM_EXPLICIT, LVM_DECODE, LVM_TARGET, LVM_MEM,
                 LVM_REGION, LVM_STACK_FAULT, LVM_DIVISION };
struct lvm_frame { uint64_t pc, regs[16]; };
struct lvm {
  uint64_t pc, regs[16];
  uint8_t memory[LVM_MEMORY];
  size_t frontier, depth;
  struct lvm_frame stack[LVM_STACK];
  enum lvm_status status;
  enum lvm_fault fault;
};
struct lvm_code {
  const uint8_t *bytes;
  size_t size;
  uint8_t *boundary;
  size_t *owner;
};
struct lvm_instruction { unsigned op, d, a, b, width; uint64_t imm; };
int lvm_decode(const struct lvm_code *, uint64_t, struct lvm_instruction *);
int lvm_code_init(struct lvm_code *, const uint8_t *, size_t);
void lvm_code_destroy(struct lvm_code *);
int lvm_verify(const struct lvm_code *, uint64_t *);
void lvm_step(struct lvm *, const struct lvm_code *);
#endif
