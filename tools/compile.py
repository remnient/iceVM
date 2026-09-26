import argparse
from pathlib import Path
import subprocess
import tempfile
from disasm import disassemble
from source import source_certificate


def compile_bytes(text):
    model = Path(__file__).resolve().parents[1] / 'build/model'
    if not model.is_file():
        raise ValueError('build the verified backend with make build/model')
    with tempfile.NamedTemporaryFile(mode='wb') as source, tempfile.NamedTemporaryFile(mode='w') as certificate:
        source.write(text.encode('ascii'))
        source.flush()
        certificate.write(source_certificate(text))
        certificate.flush()
        try:
            result = subprocess.run([str(model), source.name, '--compile-text', certificate.name],
                                    capture_output=True, check=True)
        except subprocess.CalledProcessError as error:
            raise ValueError(error.stderr.decode().strip()) from error
        return result.stdout


def compile_source(text):
    return disassemble(compile_bytes(text))


def main():
    p = argparse.ArgumentParser()
    p.add_argument('source', type=Path)
    p.add_argument('output', type=Path)
    p.add_argument('--assembly', action='store_true')
    args = p.parse_args()
    try:
        data = compile_bytes(args.source.read_bytes().decode('ascii'))
        if args.assembly:
            args.output.write_text(disassemble(data))
        else:
            args.output.write_bytes(data)
    except (ValueError, SyntaxError, OSError) as error:
        p.exit(1, f'{error}\n')


if __name__ == '__main__':
    main()
