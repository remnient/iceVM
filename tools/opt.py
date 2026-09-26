import argparse
from pathlib import Path
import subprocess
import tempfile
from isa import decode, encode, verify, MASK


def calculate(op, x, y):
    if op == 'div' and y == 0:
        return None
    return {
        'add': lambda: (x + y) & MASK, 'sub': lambda: (x - y) & MASK,
        'mul': lambda: (x * y) & MASK, 'div': lambda: x // y,
        'and': lambda: x & y, 'or': lambda: x | y, 'xor': lambda: x ^ y,
        'shl': lambda: (x << (y & 63)) & MASK, 'shr': lambda: x >> (y & 63),
        'eq': lambda: int(x == y), 'lt': lambda: int(x < y),
    }[op]()


def certify(before, after):
    model = Path(__file__).resolve().parents[1] / 'build/model'
    if not model.is_file():
        raise ValueError('build the verified checker with make build/model')
    with tempfile.NamedTemporaryFile() as source, tempfile.NamedTemporaryFile() as target:
        source.write(before)
        source.flush()
        target.write(after)
        target.flush()
        result = subprocess.run([str(model), source.name, '--validate-opt', target.name],
                                capture_output=True, text=True, check=True)
    if result.stdout.strip() != 'true':
        raise ValueError('Rocq rejected the optimisation certificate')


def rewrite_pass(data, kind):
    rows = decode(data)
    targets = {args[-1] for _, name, args in rows if name in ('jmp', 'jnz', 'call')}
    out = bytearray(data)
    index = 0
    while index < len(rows):
        pc, name, args = rows[index]
        index += 1
        if kind == 'move' and name == 'mov' and args[0] == args[1]:
            out[pc:pc + 3] = encode('pad', [3])
        if name != 'li' or index == len(rows):
            continue
        p, op, operands = rows[index]
        if p in targets:
            continue
        d, x = args
        if kind == 'store' and op == 'li' and operands[0] == d:
            out[pc:pc + 10] = encode('pad', [10])
            index += 1
        elif kind == 'constant' and op in ('add', 'sub', 'mul', 'div', 'and', 'or', 'xor', 'shl', 'shr', 'eq', 'lt'):
            if operands == [d, d, d]:
                v = calculate(op, x, x)
                if v is not None:
                    out[pc:pc + 10] = encode('li', [d, v])
                    out[p:p + 4] = encode('pad', [4])
                    index += 1
        elif kind == 'branch' and op == 'jnz' and operands[0] == d and x == 0:
            out[p:p + 10] = encode('pad', [10])
            index += 1
    return bytes(out)


def optimise(data):
    if not verify(data):
        raise ValueError('input bytecode fails structural verification')
    if any(name == 'ijmp' for _, name, _ in decode(data)):
        return data
    for kind in ('constant', 'store', 'move', 'branch'):
        result = rewrite_pass(data, kind)
        if result != data:
            certify(data, result)
        data = result
    return data


def main():
    p = argparse.ArgumentParser()
    p.add_argument('source', type=Path)
    p.add_argument('output', type=Path)
    args = p.parse_args()
    try:
        args.output.write_bytes(optimise(args.source.read_bytes()))
    except (ValueError, OSError) as e:
        p.exit(1, f'{e}\n')


if __name__ == '__main__':
    main()
