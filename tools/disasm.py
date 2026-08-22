import argparse
from pathlib import Path
from isa import OPS, decode


def disassemble(data):
    rows = decode(data)
    starts = {p for p, _, _ in rows}
    targets = {args[-1] for _, name, args in rows if name in ('jmp', 'jnz', 'call')}
    labels = starts & targets
    lines = []
    for pc, name, args in rows:
        if pc in labels:
            lines.append(f'L{pc}:')
        values = []
        for kind, value in zip(OPS[name][1], args):
            values.append(f'r{value}' if kind == 'r' else
                          f'L{value}' if name in ('jmp', 'jnz', 'call') and value in labels else hex(value))
        lines.append('  ' + name + (' ' + ', '.join(values) if values else ''))
    return '\n'.join(lines) + '\n'


def main():
    p = argparse.ArgumentParser()
    p.add_argument('source', type=Path)
    args = p.parse_args()
    try:
        print(disassemble(args.source.read_bytes()), end='')
    except (ValueError, OSError) as e:
        p.exit(1, f'{e}\n')


if __name__ == '__main__':
    main()
