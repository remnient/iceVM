import json
import os
from pathlib import Path
import random
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
from asm import assemble
from disasm import disassemble
from isa import encode, verify

VM = os.environ.get('ICEVM', str(ROOT / 'build/iceVM'))
MODEL = str(ROOT / 'build/model')
COUNT = 0


def invoke(command):
    return subprocess.run(command, capture_output=True, text=True, timeout=30)


def check(data, fuel=200, expected=None, accepted=None, trace=False, fault=None):
    global COUNT
    with tempfile.NamedTemporaryFile(suffix='.ivm') as f:
        f.write(data)
        f.flush()
        c = invoke([VM, f.name, str(fuel), '--raw'] + (['--trace'] if trace else []))
        r = invoke([MODEL, f.name, str(fuel)] + (['--trace'] if trace else []))
        assert c.returncode in (0, 1, 3), c.stderr
        assert 'Sanitizer' not in c.stderr and 'runtime error:' not in c.stderr, c.stderr
        assert r.returncode == 0, r.stderr
        cs = [json.loads(s) for s in c.stdout.splitlines()]
        rs = [json.loads(s) for s in r.stdout.splitlines()]
        assert cs == rs, (COUNT, cs[-1], rs[-1])
        if expected is not None:
            assert cs[-1]['regs'][0] == expected, cs[-1]
        if fault is not None:
            assert cs[-1]['status'] == 'fault' and cs[-1]['fault'] == fault
        v = invoke([MODEL, f.name, '--verify'])
        assert v.returncode == 0, v.stderr
        assert verify(data) == (v.stdout.strip() == 'true')
        cv = invoke([VM, f.name, str(fuel)])
        assert (cv.returncode != 2) == (v.stdout.strip() == 'true'), (COUNT, cv.stderr, v.stdout)
        if accepted is not None:
            assert (v.stdout.strip() == 'true') == accepted, (COUNT, cv.stderr)
    COUNT += 1


for path in sorted((ROOT / 'examples').glob('*.asm')):
    data = assemble(path.read_text())
    assert assemble(disassemble(data)) == data
    expected = {'factorial': 3628800, 'loop': 5050, 'memory': 42, 'indirect': 42}[path.stem]
    check(data, 400, expected, True, trace=True)

for data in (b'', b'\xff', b'\x04\x10' + bytes(8), b'\x10\x00\x01', b'\x02',
             assemble('entry\nret'), assemble('entry\njmp 2\nhalt'),
             assemble('entry\ncall 0\nhalt')):
    check(data, accepted=False)

for text, fault in (
    ('entry\ntrap', 0),
    ('entry\nli r1, 0\ndiv r0, r0, r1\nhalt', 6),
    ('entry\nload r0, r0\nhalt', 3),
    ('entry\nli r1, -1\nalloc r0, r1\nhalt', 3),
    ('entry\nli r1, -1\nload r0, r1\nhalt', 3),
    ('entry\nli r1, 1\nreset r1\nhalt', 4),
    ('entry\nli r1, -1\nijmp r1', 2),
    ('entry\ncall f\nhalt\nf: entry\ncall f\nret', 5),
):
    check(assemble(text), 600, accepted=True, fault=fault)

rng = random.Random(0x10_05_E)
values = [0, 1, 7, 63, 64, 65, (1 << 63) - 1, 1 << 63, (1 << 64) - 1]
for op in 'add sub mul div and or xor shl shr eq lt'.split():
    for _ in range(12):
        x, y = rng.choice(values + [rng.getrandbits(64)]), rng.choice(values + [rng.getrandbits(64)])
        text = f'entry\nli r1, {x}\nli r2, {y}\n{op} r0, r1, r2\nhalt'
        check(assemble(text), accepted=True, trace=True)

for _ in range(25):
    text = 'entry\nmark r8\nli r1, 32\nalloc r2, r1\n'
    for _ in range(8):
        text += f'li r3, {rng.getrandbits(64)}\nstore r2, r3\nload r0, r2\n'
    text += 'reset r8\nalloc r2, r1\nload r0, r2\nhalt'
    check(assemble(text), expected=0, accepted=True)

for _ in range(40):
    data = bytes(rng.randrange(256) for _ in range(rng.randrange(1, 45)))
    check(data, 10)

print(f'{COUNT} C/model differential cases passed')

from compile import compile_bytes
from source import serialise_source
from opt import optimise


def check_source(text, expected=None, fault=None):
    data = compile_bytes(text)
    with tempfile.NamedTemporaryFile(suffix='.ivm') as target, tempfile.NamedTemporaryFile(mode='w', suffix='.sexp') as source:
        target.write(data)
        target.flush()
        source.write(serialise_source(text))
        source.flush()
        c = invoke([VM, target.name, '10000'])
        r = invoke([MODEL, source.name, '100000', '--source'])
        assert c.returncode in (0, 1), c.stderr
        assert r.returncode == 0, r.stderr
        cs, rs = json.loads(c.stdout), json.loads(r.stdout)
        observed = {key: cs[key] for key in ('status', 'fault', 'frontier', 'memory')}
        assert observed == {key: rs[key] for key in observed}, (cs['pc'], rs)
        if cs['status'] == 'stopped':
            assert cs['regs'][0] == rs['result'], (cs['regs'][0], rs['result'])
        if expected is not None:
            assert cs['regs'][0] == expected
        if fault is not None:
            assert cs['status'] == 'fault' and cs['fault'] == fault
    check(data, 10000, expected, True)
    check_optimisation(data)


def check_optimisation(data):
    transformed = optimise(data)
    assert len(transformed) == len(data)
    with tempfile.NamedTemporaryFile() as a, tempfile.NamedTemporaryFile() as b:
        a.write(data)
        a.flush()
        b.write(transformed)
        b.flush()
        ca, cb = invoke([VM, a.name]), invoke([VM, b.name])
        assert ca.returncode in (0, 1) and ca.returncode == cb.returncode, (ca.stderr, cb.stderr)
        assert json.loads(ca.stdout) == json.loads(cb.stdout)
    check(transformed, 10000, accepted=True)


for path in sorted((ROOT / 'examples').glob('*.ls')):
    check_source(path.read_text(), {'factorial': 3628800, 'regions': 45}[path.stem])

for x in (0, 1, 63, 64, (1 << 63), (1 << 64) - 1):
    for op in ('+', '-', '*', '//', '&', '|', '^', '<<', '>>', '<', '>=', '==', '!='):
        y = rng.randrange(1, 80)
        check_source(f'def main():\n    x = {x}\n    y = {y}\n    return x {op} y\n')

for expression in ('-7', '~9', 'not 0', 'not 42', 'helper(3) + helper(5)',
                   'load(alloc(8))', '1 + load(alloc(8))', 'alloc(8) > alloc(8)',
                   'alloc(8) <= alloc(8)', 'alloc(8) >= alloc(8)', 'alloc(8) < alloc(8)'):
    check_source(f'def main():\n    return {expression}\ndef helper(n):\n    return n * 2\n')

for text, fault in (
    ('def main():\n    return 1 // 0\n', 6),
    ('def main():\n    return load(0)\n', 3),
    ('def main():\n    return alloc(-1)\n', 3),
    ('def main():\n    reset(1)\n    return 0\n', 4),
):
    check_source(text, fault=fault)

for text in (
    'entry\nli r0, 3\nadd r0, r0, r0\nhalt',
    'entry\nli r0, 3\nli r0, 7\nhalt',
    'entry\nmov r0, r0\nhalt',
    'entry\nli r1, 0\njnz r1, yes\nli r0, 7\nhalt\nyes: trap',
    'entry\nli r1, 1\njnz r1, yes\ntrap\nyes: li r0, 7\nhalt',
    'entry\nli r0, 0\ndiv r0, r0, r0\nhalt',
    'entry\nli r0, 9\njmp join\nli r0, 7\njoin: add r0, r0, r0\nhalt',
):
    check_optimisation(assemble(text))

for bad in ('mov r16, r0', 'li r0, missing', 'li r0, 0x10000000000000000', 'x: halt\nx: halt'):
    try:
        assemble(bad)
        raise AssertionError('invalid assembly accepted')
    except ValueError:
        pass

for data in (b'\x02\x1b', b'\x02\x1b\x09' + bytes(9), b'\x02\x1b\x08',
             assemble('entry\njmp f\nf: entry\nret'),
             assemble('entry\nnop\nf: entry\nret'),
             assemble('entry\ncall f\nhalt\nf: entry\nhalt')):
    check(data, accepted=False)

for address in (0, 1, 7, 8, 16, 24):
    text = f'entry\nli r1, 32\nalloc r2, r1\nli r2, {address}\nli r3, 0x0102030405060708\nstore r2, r3\nload r0, r2\nhalt'
    check(assemble(text), expected=0x0102030405060708, accepted=True, trace=True)

for text, fault in (
    ('entry\nli r1, 32\nalloc r2, r1\nli r2, 25\nload r0, r2\nhalt', 3),
    ('entry\nli r1, 32\nalloc r2, r1\nli r2, 25\nstore r2, r0\nhalt', 3),
    ('entry\nli r1, -1\nreset r1\nhalt', 4),
):
    check(assemble(text), accepted=True, fault=fault)
check(assemble('entry\nli r1, 65536\nalloc r2, r1\nli r1, 0\nalloc r0, r1\nhalt'), expected=65536, accepted=True)

for op in 'add sub mul div and or xor shl shr eq lt'.split():
    for value in (0, 63, (1 << 64) - 1):
        check_optimisation(assemble(f'entry\nli r0, {value}\n{op} r0, r0, r0\nhalt'))

print(f'{COUNT} total C/model cases plus source/model and optimisation comparisons passed')


def accepted_certificate(before, after, source=None):
    with tempfile.NamedTemporaryFile(mode='w' if source is not None else 'w+b') as a, tempfile.NamedTemporaryFile() as b:
        if source is None:
            a.write(before)
        else:
            a.write(serialise_source(source))
        a.flush()
        b.write(after)
        b.flush()
        option = '--validate-opt' if source is None else '--validate-compiler'
        result = invoke([MODEL, a.name, option, b.name])
        assert result.returncode == 0, result.stderr
        return result.stdout.strip() == 'true'


source = 'def main():\n    return 42\n'
compiled = compile_bytes(source)
assert accepted_certificate(None, compiled, source)
for index in (3, len(compiled) - 1):
    changed = bytearray(compiled)
    changed[index] ^= 1
    assert not accepted_certificate(None, bytes(changed), source)

from isa import decode

old = assemble('entry\nli r0, 3\nadd r0, r0, r0\nhalt')
new = optimise(old)
assert accepted_certificate(old, new)
wrong = bytearray(new)
wrong[3] = 7
assert not accepted_certificate(old, bytes(wrong))

for old_text, op in (
    ('entry\nli r0, 0\ndiv r0, r0, r0\nhalt', 'div'),
    ('entry\nli r1, 8\nalloc r2, r1\nhalt', 'alloc'),
    ('entry\nli r1, 8\nalloc r2, r1\nstore r2, r0\nhalt', 'store'),
    ('entry\nli r1, 1\njnz r1, target\ntrap\ntarget: halt', 'jnz'),
):
    old = assemble(old_text)
    changed = bytearray(old)
    for pc, name, args in decode(old):
        if name == op:
            size = len(encode(name, args))
            changed[pc:pc + size] = encode('pad', [size])
    assert not accepted_certificate(old, bytes(changed))

old = assemble('entry\nli r0, 3\njmp interior\nli r0, 4\ninterior: add r0, r0, r0\nhalt')
changed = bytearray(old)
for pc, name, args in decode(old):
    if name == 'li' and args == [0, 4]:
        changed[pc:pc + 10] = encode('li', [0, 8])
    if name == 'add':
        changed[pc:pc + 4] = encode('pad', [4])
assert not accepted_certificate(old, bytes(changed))

check_source('''def main():
    return even(20)
def even(n):
    if n == 0:
        return 1
    return odd(n - 1)
def odd(n):
    if n == 0:
        return 0
    return even(n - 1)
''', 1)
check_source('''def main():
    base = mark()
    p = alloc(8)
    store(p, 7)
    result = increment(p) + load(p)
    reset(base)
    return result
def increment(p):
    store(p, load(p) + 1)
    return load(p)
''', 16)
check_source('''def main():
    p = alloc(8)
    touch(p)
    return load(p)
def touch(p):
    store(p, 9)
    return 0
''', 9)
check_source('''def main():
    i = 0
    while alloc(8) < 24:
        i = i + 1
    return i
''', 3)
check_source('''def main():
    i = 0
    while i < 10:
        if i == 4:
            return i
        i = i + 1
    return 99
''', 4)
check(compile_bytes('def main():\n    while True:\n        pass\n'), 60, accepted=True)

check_source('''def main():
    p = alloc(8)
    store(p, 11)
    return fail(p) + overwrite(p)
def fail(p):
    return load(p) // 0
def overwrite(p):
    store(p, 99)
    return 0
''', fault=6)
check_source('''def main():
    return recur(0)
def recur(n):
    return recur(n + 1)
''', fault=5)
check_source('''def main():
    p = alloc(8)
    i = 0
    while i < 4:
        store(p, i)
        if i == 3:
            return load(p + 8)
        i = i + 1
    return 0
''', fault=3)
check_source('''def main():
    p = alloc(8)
    return bad_reset(p)
def bad_reset(p):
    reset(p + 9)
    return 0
''', fault=4)

for invalid in (
    'def main():\n    return missing\n',
    'def main():\n    return main()\n',
    'def main():\n    return 1.5\n',
    'def main():\n    return 1 and 2\n',
    'def main():\n    return 1 + (2 + (3 + (4 + (5 + (6 + 7)))))\n',
):
    try:
        compile_bytes(invalid)
        raise AssertionError('invalid source accepted')
    except ValueError:
        pass

from source import source_certificate


def compile_certificate(text, certificate):
    with tempfile.NamedTemporaryFile(mode='w') as raw, tempfile.NamedTemporaryFile(mode='w') as cert:
        raw.write(text)
        raw.flush()
        cert.write(certificate)
        cert.flush()
        return subprocess.run([MODEL, raw.name, '--compile-text', cert.name], capture_output=True, timeout=30)


text = 'def main():\n    return 1 + 2 * 3\n'
certificate = source_certificate(text)
assert compile_certificate(text, certificate).returncode == 0
for changed in (
    certificate.replace('(literal 2)', '(literal 9)'),
    certificate.replace('binary add', 'binary sub'),
    certificate.replace('binary mul', 'binary add'),
    certificate.replace('(109 97 105 110)', '(111 116 104 101 114)'),
):
    assert compile_certificate(text, changed).returncode != 0
for changed in (
    text.replace('1 + 2', '1 - 2'),
    text.replace('2 * 3', '(2 * 3)'),
    text + '    return 0\n',
    text.replace('    return', 'return'),
    text.replace('2 * 3', '2 * 3 + 4'),
):
    assert compile_certificate(changed, certificate).returncode != 0
check_source('def main():\n    return 18446744073709551617\n', 1)
check_source('def main():\n    return 0x_2a + 0b10 + 0o10\n', 52)

check_source('def main():\r\n    return 42\r\n', 42)

with tempfile.NamedTemporaryFile() as raw, tempfile.NamedTemporaryFile() as output:
    raw.write(b'def main():\r    return 42\r')
    raw.flush()
    result = invoke([sys.executable, str(ROOT / 'tools/compile.py'), raw.name, output.name])
    assert result.returncode != 0

print(f'{COUNT} C/model cases; source and bytecode certificate rejection checks passed')
