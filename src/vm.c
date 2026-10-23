#include "vm.h"
#include <stdlib.h>
#include <limits.h>

_Static_assert(CHAR_BIT == 8, "iceVM requires octets");
_Static_assert(SIZE_MAX >= UINT32_MAX, "iceVM requires 32-bit size_t");

static uint64_t read64(const uint8_t *p) {
  uint64_t v = 0;
  for (unsigned i = 0; i < 8; i++) v += (uint64_t)p[i] << (8 * i);
  return v;
}

int icevm_decode(const struct icevm_code *c, uint64_t pc, struct icevm_instruction *i) {
  if (pc >= c->size) return 0;
  const uint8_t *p = c->bytes + (size_t)pc;
  i->op = p[0];
  i->d = i->a = i->b = i->width = 0;
  i->imm = 0;
  switch (i->op) {
    case 0: case 1: case 2: case 3: case 15:
      i->width = 1;
      return 1;
    case 4: case 12:
      if (c->size - (size_t)pc < 10) return 0;
      i->width = 10;
      i->d = p[1];
      i->imm = read64(p + 2);
      return i->d < 16;
    case 5: case 6: case 7: case 8:
      if (c->size - (size_t)pc < 3) return 0;
      i->width = 3;
      i->d = p[1];
      i->a = p[2];
      return i->d < 16 && i->a < 16;
    case 9: case 10: case 13:
      if (c->size - (size_t)pc < 2) return 0;
      i->width = 2;
      i->d = p[1];
      return i->d < 16;
    case 11: case 14:
      if (c->size - (size_t)pc < 9) return 0;
      i->width = 9;
      i->imm = read64(p + 1);
      return 1;
    case 27:
      if (c->size - (size_t)pc < 2 || p[1] > 8) return 0;
      i->width = 2U + p[1];
      return i->width <= c->size - (size_t)pc;
    default:
      if (i->op < 16 || i->op > 26 || c->size - (size_t)pc < 4) return 0;
      i->width = 4;
      i->d = p[1];
      i->a = p[2];
      i->b = p[3];
      return i->d < 16 && i->a < 16 && i->b < 16;
  }
}

int icevm_code_init(struct icevm_code *c, const uint8_t *bytes, size_t size) {
  c->bytes = bytes;
  c->size = size;
  c->boundary = NULL;
  c->owner = NULL;
  if (size > UINT32_MAX || size > SIZE_MAX / sizeof(size_t)) return 0;
  c->boundary = calloc(size ? size : 1, 1);
  c->owner = calloc(size ? size : 1, sizeof(size_t));
  if (!c->boundary || !c->owner) {
    icevm_code_destroy(c);
    return 0;
  }
  size_t p = 0, owner = 0;
  struct icevm_instruction i;
  while (icevm_decode(c, p, &i)) {
    if (i.op == 2) owner = p;
    c->boundary[p] = 1;
    c->owner[p] = owner;
    p += i.width;
  }
  return 1;
}

void icevm_code_destroy(struct icevm_code *c) {
  free(c->boundary);
  free(c->owner);
  c->boundary = NULL;
  c->owner = NULL;
}

static int boundary(const struct icevm_code *c, uint64_t p) {
  return p < c->size && c->boundary[(size_t)p];
}

static int local(const struct icevm_code *c, uint64_t p, uint64_t t) {
  return boundary(c, p) && boundary(c, t) && c->owner[(size_t)p] == c->owner[(size_t)t];
}

static int callable(const struct icevm_code *c, uint64_t t) {
  return t != 0 && boundary(c, t) && c->bytes[(size_t)t] == 2 && c->owner[(size_t)t] != 0;
}

int icevm_verify(const struct icevm_code *c, uint64_t *bad) {
  size_t p = 0;
  struct icevm_instruction i;
  if (!c->size || c->bytes[0] != 2) { *bad = 0; return 0; }
  while (p < c->size) {
    *bad = p;
    if (!icevm_decode(c, p, &i) || !boundary(c, p)) return 0;
    size_t n = p + i.width;
    switch (i.op) {
      case 0: if (c->owner[p] != 0) return 0; break;
      case 1: case 13: break;
      case 3: if (c->owner[p] == 0) return 0; break;
      case 11: if (!local(c, p, i.imm)) return 0; break;
      case 12:
        if (!local(c, p, i.imm) || !local(c, p, n)) return 0;
        break;
      case 14:
        if (!callable(c, i.imm) || !local(c, p, n)) return 0;
        break;
      default: if (!local(c, p, n)) return 0; break;
    }
    p = n;
  }
  return 1;
}

static void trap(struct icevm *s, enum icevm_fault f) {
  s->status = ICEVM_FAULT;
  s->fault = f;
}

void icevm_step(struct icevm *s, const struct icevm_code *c) {
  if (s->status != ICEVM_RUNNING) return;
  struct icevm_instruction i;
  if (!icevm_decode(c, s->pc, &i)) { trap(s, ICEVM_DECODE); return; }
  uint64_t next = s->pc + i.width;
  uint64_t x = s->regs[i.a], y = s->regs[i.b], v = 0, address;
  switch (i.op) {
    case 0: s->status = ICEVM_STOPPED; return;
    case 1: trap(s, ICEVM_EXPLICIT); return;
    case 2: case 15: case 27: break;
    case 3:
      if (!s->depth) { trap(s, ICEVM_STACK_FAULT); return; }
      if (!boundary(c, s->stack[s->depth - 1].pc)) { trap(s, ICEVM_TARGET); return; }
      v = s->regs[0];
      s->depth--;
      for (unsigned r = 0; r < 16; r++) s->regs[r] = s->stack[s->depth].regs[r];
      s->regs[0] = v;
      next = s->stack[s->depth].pc;
      break;
    case 4: s->regs[i.d] = i.imm; break;
    case 5: s->regs[i.d] = x; break;
    case 6:
      address = x;
      if (address > s->frontier || s->frontier - address < 8) { trap(s, ICEVM_MEM); return; }
      s->regs[i.d] = read64(s->memory + (size_t)address);
      break;
    case 7:
      address = s->regs[i.d];
      if (address > s->frontier || s->frontier - address < 8) { trap(s, ICEVM_MEM); return; }
      for (unsigned b = 0; b < 8; b++) s->memory[(size_t)address + b] = (uint8_t)(x >> (8 * b));
      break;
    case 8:
      if (x > ICEVM_MEMORY - s->frontier) { trap(s, ICEVM_MEM); return; }
      v = s->frontier;
      for (size_t b = 0; b < x; b++) s->memory[s->frontier + b] = 0;
      s->frontier += (size_t)x;
      s->regs[i.d] = v;
      break;
    case 9: s->regs[i.d] = s->frontier; break;
    case 10:
      if (s->regs[i.d] > s->frontier) { trap(s, ICEVM_REGION); return; }
      s->frontier = (size_t)s->regs[i.d];
      break;
    case 11:
      next = i.imm;
      if (!local(c, s->pc, next)) { trap(s, ICEVM_TARGET); return; }
      break;
    case 12:
      if (!s->regs[i.d]) break;
      next = i.imm;
      if (!local(c, s->pc, next)) { trap(s, ICEVM_TARGET); return; }
      break;
    case 13:
      next = s->regs[i.d];
      if (!local(c, s->pc, next)) { trap(s, ICEVM_TARGET); return; }
      break;
    case 14:
      if (!callable(c, i.imm) || !local(c, s->pc, next)) { trap(s, ICEVM_TARGET); return; }
      if (s->depth == ICEVM_STACK) { trap(s, ICEVM_STACK_FAULT); return; }
      s->stack[s->depth].pc = next;
      for (unsigned r = 0; r < 16; r++) s->stack[s->depth].regs[r] = s->regs[r];
      s->depth++;
      next = i.imm;
      break;
    case 16: v = x + y; break;
    case 17: v = x - y; break;
    case 18: v = x * y; break;
    case 19:
      if (!y) { trap(s, ICEVM_DIVISION); return; }
      v = x / y;
      break;
    case 20: v = x & y; break;
    case 21: v = x | y; break;
    case 22: v = x ^ y; break;
    case 23: v = x << (y & 63); break;
    case 24: v = x >> (y & 63); break;
    case 25: v = x == y; break;
    case 26: v = x < y;
      break;
  }
  if (i.op >= 16 && i.op <= 26) s->regs[i.d] = v;
  s->pc = next;
}
