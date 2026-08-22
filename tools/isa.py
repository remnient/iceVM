import struct

OPS = {
    'halt': (0, ''), 'trap': (1, ''), 'entry': (2, ''), 'ret': (3, ''),
    'li': (4, 'rq'), 'mov': (5, 'rr'), 'load': (6, 'rr'),
    'store': (7, 'rr'), 'alloc': (8, 'rr'), 'mark': (9, 'r'),
    'reset': (10, 'r'), 'jmp': (11, 'q'), 'jnz': (12, 'rq'),
    'ijmp': (13, 'r'), 'call': (14, 'q'), 'nop': (15, ''), 'pad': (27, 'p'),
}
for number, name in enumerate('add sub mul div and or xor shl shr eq lt'.split(), 16):
    OPS[name] = (number, 'rrr')
BY_CODE = {op: (name, fmt) for name, (op, fmt) in OPS.items()}
MASK = (1 << 64) - 1


def width(name):
    return 1 + sum(8 if x == 'q' else 1 for x in OPS[name][1])


def encode(name, args):
    op, fmt = OPS[name]
    if name == 'pad':
        if len(args) != 1 or not 2 <= args[0] <= 10:
            raise ValueError('pad width must be between 2 and 10')
        return bytes([27, args[0] - 2]) + bytes(args[0] - 2)
    if len(args) != len(fmt):
        raise ValueError(f'{name} expects {len(fmt)} operands')
    out = bytearray([op])
    for kind, value in zip(fmt, args):
        if kind == 'r':
            if not 0 <= value < 16:
                raise ValueError(f'invalid register {value}')
            out.append(value)
        else:
            if not 0 <= value <= MASK:
                raise ValueError(f'operand outside uint64: {value}')
            out.extend(struct.pack('<Q', value))
    return bytes(out)


def decode(data):
    p = 0
    result = []
    while p < len(data):
        start = p
        if data[p] not in BY_CODE:
            raise ValueError(f'invalid opcode at {p}')
        name, fmt = BY_CODE[data[p]]
        if name == 'pad':
            if p + 2 > len(data) or data[p + 1] > 8 or p + 2 + data[p + 1] > len(data):
                raise ValueError(f'invalid padding at {p}')
            n = 2 + data[p + 1]
            result.append((p, name, [n]))
            p += n
            continue
        p += 1
        args = []
        for kind in fmt:
            n = 1 if kind == 'r' else 8
            if p + n > len(data):
                raise ValueError(f'truncated instruction at {start}')
            v = int.from_bytes(data[p:p + n], 'little')
            if kind == 'r' and v >= 16:
                raise ValueError(f'invalid register at {start}')
            args.append(v)
            p += n
        result.append((start, name, args))
    return result


def verify(data):
    try:
        rows = decode(data)
    except ValueError:
        return False
    if not rows or rows[0][1] != 'entry':
        return False
    by_pc = {pc: (name, args) for pc, name, args in rows}
    owners = {}
    owner = 0
    for pc, name, _ in rows:
        if name == 'entry':
            owner = pc
        owners[pc] = owner

    def local(p, t):
        return t in owners and owners[p] == owners[t]

    for index, (pc, name, args) in enumerate(rows):
        next_pc = rows[index + 1][0] if index + 1 < len(rows) else len(data)
        if name == 'halt':
            if owners[pc] != 0:
                return False
        elif name == 'ret':
            if owners[pc] == 0:
                return False
        elif name in ('trap', 'ijmp'):
            pass
        elif name == 'jmp':
            if not local(pc, args[0]):
                return False
        elif name == 'jnz':
            if not local(pc, args[1]) or not local(pc, next_pc):
                return False
        elif name == 'call':
            t = args[0]
            if t == 0 or t not in by_pc or by_pc[t][0] != 'entry' or not local(pc, next_pc):
                return False
        elif not local(pc, next_pc):
            return False
    return True
