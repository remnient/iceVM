import argparse
import re
from pathlib import Path
from isa import OPS, MASK, width, encode


def assemble(text):
    labels, rows, pc = {}, [], 0
    for line_no, line in enumerate(text.splitlines(), 1):
        line = line.split(';', 1)[0].strip()
        if not line:
            continue
        if ':' in line:
            label, line = line.split(':', 1)
            label = label.strip()
            if not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*', label) or label in labels:
                raise ValueError(f'line {line_no}: invalid or duplicate label')
            labels[label] = pc
            line = line.strip()
            if not line:
                continue
        fields = line.replace(',', ' ').split()
        name, operands = fields[0], fields[1:]
        if name not in OPS or len(operands) != len(OPS[name][1]):
            raise ValueError(f'line {line_no}: invalid instruction')
        rows.append((line_no, name, operands))
        pc += int(operands[0], 0) if name == 'pad' else width(name)
    out = bytearray()
    for line_no, name, operands in rows:
        args = []
        for kind, operand in zip(OPS[name][1], operands):
            if kind == 'r':
                if not re.fullmatch(r'r(?:[0-9]|1[0-5])', operand):
                    raise ValueError(f'line {line_no}: invalid register {operand}')
                args.append(int(operand[1:]))
            else:
                try:
                    value = labels[operand] if operand in labels else int(operand, 0)
                except ValueError as e:
                    raise ValueError(f'line {line_no}: unknown operand {operand}') from e
                if not -(1 << 63) <= value <= MASK:
                    raise ValueError(f'line {line_no}: immediate outside 64 bits')
                args.append(value & MASK)
        out.extend(encode(name, args))
    return bytes(out)


def main():
    p = argparse.ArgumentParser()
    p.add_argument('source', type=Path)
    p.add_argument('output', type=Path)
    args = p.parse_args()
    try:
        args.output.write_bytes(assemble(args.source.read_text()))
    except (ValueError, OSError) as e:
        p.exit(1, f'{e}\n')


if __name__ == '__main__':
    main()
