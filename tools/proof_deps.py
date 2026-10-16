import argparse
import os
from pathlib import Path
import shlex
import shutil
import subprocess

COMPCERT_REVISION = '14d616046360a0b2611ebdfc2f98368af402e1f7'
VST_REVISION = '3c37c2e2b574e23aee8fdd1684aa0ffed227491e'


def run(args, cwd=None, env=None):
    subprocess.run(args, cwd=cwd, env=env, check=True)


def checkout(path, url, revision):
    if not path.exists():
        path.mkdir(parents=True)
        run(['git', 'init', str(path)])
        run(['git', 'remote', 'add', 'origin', url], cwd=path)
        run(['git', 'fetch', '--depth=1', 'origin', revision], cwd=path)
        run(['git', 'checkout', '--detach', 'FETCH_HEAD'], cwd=path)
    actual = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=path, text=True).strip()
    if actual != revision:
        raise ValueError(f'{path} has revision {actual}, expected {revision}')
    run(['git', 'diff', '--exit-code', 'HEAD', '--'], cwd=path)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--cache', type=Path, default=Path.home() / '.cache')
    parser.add_argument('--rocq', default=shutil.which('rocq'))
    parser.add_argument('--jobs', type=int, default=2)
    parser.add_argument('--menhir', default=shutil.which('menhir'))
    args = parser.parse_args()
    if not args.rocq or args.jobs < 1:
        parser.error('provide a Rocq executable and a positive job count')
    args.cache = args.cache.expanduser().resolve()
    rocq = str(Path(shutil.which(args.rocq) or args.rocq).resolve())
    compcert = args.cache / 'loosevm-compcert-3.18'
    vst = args.cache / 'loosevm-vst-2.17'
    shims = args.cache / 'loosevm-proof-bin'
    checkout(compcert, 'https://github.com/AbsInt/CompCert.git', COMPCERT_REVISION)
    checkout(vst, 'https://github.com/PrincetonUniversity/VST.git', VST_REVISION)
    shims.mkdir(parents=True, exist_ok=True)
    for executable, command in {'coqc': 'compile', 'coqtop': 'repl', 'coqdep': 'dep',
                                'coqchk': 'check', 'coqdoc': 'doc'}.items():
        script = shims / executable
        script.write_text(f'#!/bin/sh\nexec {shlex.quote(rocq)} {command} "$@"\n')
        script.chmod(0o755)
    if args.menhir:
        script = shims / 'menhir'
        menhir = Path(shutil.which(args.menhir) or args.menhir).resolve()
        if menhir != script.resolve():
            script.write_text(f'#!/bin/sh\nexec {shlex.quote(str(menhir))} "$@"\n')
        script.chmod(0o755)
    env = os.environ.copy()
    env['PATH'] = os.pathsep.join((str(shims), str(Path(rocq).parent), env['PATH']))
    run(['./configure', '-clightgen', '-prefix', str(args.cache / 'loosevm-proof-install'),
         'x86_64-linux'], cwd=compcert, env=env)
    run(['make', 'depend'], cwd=compcert, env=env)
    run(['make', f'-j{args.jobs}', 'clightgen'], cwd=compcert, env=env)
    run(['make', f'-j{args.jobs}', 'COMPCERT=src_dir', f'COMPCERT_SRC_DIR={compcert}',
         'FLOCQ=bundled', 'BITSIZE=64', f'COQBIN={shims}/', 'IGNORECOQVERSION=true',
         'IGNORECOMPCERTVERSION=true', 'veric/version.vo', 'floyd/proofauto.vo'], cwd=vst, env=env)


if __name__ == '__main__':
    main()
