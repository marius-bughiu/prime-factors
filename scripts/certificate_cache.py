"""Reuse the kernel and axiom check of an identical generated factorization proof."""

from datetime import datetime, timezone
from hashlib import sha256
import json
import math
import os
from pathlib import Path
import platform
import re
import subprocess
import tempfile
from time import perf_counter


ROOT = Path(__file__).resolve().parents[1]
CONTEXT = 'PRIME_FACTORS_CERTIFICATE_CONTEXT'
CACHE = 'PRIME_FACTORS_CERTIFICATES'
MODULES = ('Certificate', 'Pratt', 'PartialOrder')


def lean_output(*args):
    return subprocess.check_output(['lake', 'env', 'lean', *args], cwd=ROOT, text=True)


def context_digest():
    """Ask Lean for imports. Project sources and compiled modules both enter the key."""
    hashes = {}
    for name in ('scripts/factor.py', 'scripts/certificate_cache.py', 'lean-toolchain',
                 'lake-manifest.json', 'lakefile.toml', 'scripts/Audit.lean'):
        hashes[name] = sha256((ROOT / name).read_bytes()).hexdigest()
    hashes['environment'] = [lean_output('--version').strip(), platform.system(),
                             platform.machine(), platform.python_version()]
    core = Path(lean_output('--print-prefix').strip()).resolve() / 'lib/lean'
    packages = (ROOT / '.lake/packages').resolve()
    library = (ROOT / '.lake/build/lib/lean').resolve()
    pending = [Path('PrimeFactors', name + '.lean') for name in MODULES]
    while pending:
        relative = pending.pop()
        name = relative.as_posix()
        if name in hashes:
            continue
        hashes[name] = sha256((ROOT / relative).read_bytes()).hexdigest()
        compiled = relative.with_suffix('.olean')
        hashes[compiled.as_posix()] = sha256((library / compiled).read_bytes()).hexdigest()
        for line in lean_output('--deps', name).splitlines():
            imported = (ROOT / line).resolve()
            if imported.is_relative_to(library):
                pending.append(imported.relative_to(library).with_suffix('.lean'))
            elif imported.is_relative_to(packages):
                key = 'packages/' + imported.relative_to(packages).as_posix()
                if key not in hashes:
                    hashes[key] = sha256(imported.read_bytes()).hexdigest()
            elif not imported.is_relative_to(core):
                raise ValueError(f'unpinned Lean dependency {imported}')
    return sha256(json.dumps(hashes, sort_keys=True).encode()).hexdigest()


def configure(directory):
    """Only the opt-in benchmark driver enables this in its factor.py subprocesses."""
    os.environ.pop(CONTEXT, None)
    os.environ.pop(CACHE, None)
    if directory is None:
        return
    try:
        context = context_digest()
    except (OSError, ValueError, subprocess.CalledProcessError) as error:
        print(f'Generated proofs will be checked directly ({error}).', flush=True)
        return
    os.environ[CONTEXT] = context
    os.environ[CACHE] = str(Path(directory).resolve() / 'certificates')


def verified_record(path, key):
    try:
        record = json.loads(path.read_bytes())
        if (isinstance(record, dict) and record.get('key') == key
                and isinstance(record.get('commit'), str)
                and re.fullmatch('[0-9a-f]{40}', record['commit'])
                and isinstance(record.get('measured_at'), str)
                and datetime.fromisoformat(record['measured_at']).tzinfo is not None
                and (record.get('run_id') is None or str(record['run_id']).isdigit())
                and isinstance(record.get('kernel_seconds'), (float, int))
                and math.isfinite(record['kernel_seconds']) and record['kernel_seconds'] >= 0):
            return record
    except (OSError, ValueError, OverflowError):
        pass
    return None


def check_generated(proof, verify):
    """Called exclusively for the canonical output just written by render_certificate."""
    context, directory = os.getenv(CONTEXT), os.getenv(CACHE)
    if not directory or not context or not re.fullmatch('[0-9a-f]{64}', context):
        verify(proof)
        return None
    key = sha256(bytes.fromhex(context) + proof.read_bytes()).hexdigest()
    dest = Path(directory) / (key + '.json')
    record = verified_record(dest, key)
    if record is not None:
        return dict(record, reused=True)

    start = perf_counter()
    verify(proof)
    seconds = perf_counter() - start
    sha = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip()
    record = dict(key=key, commit=sha, measured_at=datetime.now(timezone.utc).isoformat(timespec='seconds'),
                  run_id=os.getenv('GITHUB_RUN_ID'), kernel_seconds=seconds)
    if subprocess.check_output(['git', 'status', '--porcelain'], cwd=ROOT):
        record['local_changes_at_start'] = True
    dest.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(mode='w', dir=dest.parent, delete=False) as staged:
        json.dump(record, staged)
    os.replace(staged.name, dest)
    return dict(record, reused=False)
