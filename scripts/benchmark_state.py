"""Content-addressed benchmark rows and the exact proof sources produced with them."""

import hashlib
from datetime import datetime, timezone
import platform
import shutil
import sys
from contextlib import contextmanager
from functools import lru_cache
from importlib.metadata import PackageNotFoundError, version
import json
import os
import re
import subprocess
import tempfile
from pathlib import Path


# These methods only consume the expanded case, public code, and the pinned prover.
# For other methods include directory membership as well as observed file contents.
ISOLATED = frozenset(('fermat', 'high-word-sum-ranking', 'high-word-suffix-ranking', 'fractional-word-ranking'))
CASE_ID = re.compile(r'[A-Za-z0-9_-]+')
PROOF_NAME = re.compile(r'[A-Za-z0-9_-]+\.lean')
FORMAT = 'benchmark-rows-v1'
PROVENANCE = ('commit', 'measured_at', 'run_id', 'repository', 'platform', 'cpu', 'python', 'lean')


def encoded(value):
    return json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(',', ':'),
                      allow_nan=False).encode('utf-8')


def digest(data):
    return hashlib.sha256(data).hexdigest()


def presentation(name):
    return (Path(name).parts[0] in ('site', 'discoveries', 'docs', 'tests', '.github') or
            name in ('README.md', 'LICENSE', 'CONTRIBUTING.md', 'AGENTS.md', 'scripts/render_site.py',
                     'scripts/pages_revision.py', 'scripts/ci_lean_build.py', 'scripts/verify_checks.py'))


class Inputs:
    def __init__(self, root, shared, fixtures, lean, other=None):
        self.root = root
        self.shared = shared
        self.fixtures = fixtures
        self.lean = lean
        self.other = other or {}
        self.other_tree = digest(encoded(self.other))
        self.fixture_names = digest(encoded(sorted(fixtures)))
        self.fixture_tree = digest(encoded(fixtures))
        self.lean_tree = digest(encoded(lean))

    def snapshot(self):
        return self.shared, self.fixture_tree, self.lean_tree, self.other_tree


def input_hashes(root, runtime, ignored=()):
    """Hash the actual checkout. Unknown tracked files default to shared inputs."""
    listed = subprocess.check_output(['git', 'ls-files', '-z', '--cached', '--others',
                                      '--exclude-standard'], cwd=root)
    shared, fixtures, lean, other = {}, {}, {}, {}
    ignored = {p for p in ignored if p is not None}
    for raw in sorted(set(listed.split(b'\0')) - {b''}):
        name = os.fsdecode(raw)
        parts = Path(name).parts
        file = root / name
        if file in ignored or any(parent in ignored for parent in file.parents):
            continue
        if not file.exists():
            continue
        value = digest(file.read_bytes())
        if file.is_symlink():
            value = digest(encoded([os.readlink(file), value]))
        if presentation(name):
            other[name] = value
        elif len(parts) == 2 and parts[0] == 'benchmarks' and file.suffix == '.json':
            fixtures[name] = value
        elif name == 'PrimeFactors.lean' or (parts[0] == 'PrimeFactors' and file.suffix == '.lean'):
            lean[name] = value
        else:
            shared[name] = value
    return Inputs(root, digest(encoded([FORMAT, runtime, shared])), fixtures, lean, other)


def case_key(inputs, filename, method, case):
    return digest(encoded([inputs.shared, filename, method, case]))


# The runner is serial. Observe imports before eager experiment imports and attach
# their fixture reads to every row. No hook executes code from a restored entry.
_active = None
_installed = False


class Observed:
    def __init__(self):
        self.fixtures = set()
        self.headers = set()
        self.lean = set()
        self.other = set()
        self.opaque = False


def _audit(event, args):
    if _active is None:
        return
    root, observed = _active
    if event in ('open', 'os.listdir', 'os.scandir'):
        path = args[0] if args else None
        if not isinstance(path, (str, bytes, os.PathLike)):
            return
        path = os.fsdecode(path)
        file = Path(os.path.abspath(path))
        if not file.is_relative_to(root):
            return
        name = file.relative_to(root).as_posix()
        if name == '.' or (event != 'open' and file in (root/'PrimeFactors', root/'benchmarks')):
            observed.opaque = True
        elif file.parent == root/'benchmarks' and file.suffix == '.json':
            observed.fixtures.add(name)
        elif name == 'PrimeFactors.lean' or (name.startswith('PrimeFactors/') and file.suffix == '.lean'):
            observed.lean.add(name)
        elif presentation(name) and '__pycache__' not in file.parts:
            if event == 'open':
                observed.other.add(name)
            else:
                observed.opaque = True
    elif event == 'subprocess.Popen':
        _, args, cwd, _ = args
        if not isinstance(args, (list, tuple)):
            observed.opaque = True
            return
        args = [os.fsdecode(arg) for arg in args]
        if (len(args) >= 2 and args[0] == sys.executable and
                Path(cwd or Path.cwd()).resolve() == root and args[1] == 'scripts/factor.py' and
                '--verify' in args):
            # This audited CLI only reads canonical certificate modules if it finds factors;
            # the retained generated source supplies their actual imports.
            observed.headers.add('import PrimeFactors.Certificate')
            return
        if len(args) == 5 and args[:4] == ['lake', 'env', 'lean', '-DwarningAsError=true']:
            try:
                source = Path(cwd or Path.cwd()) / args[4]
                observed.headers.add(source.read_text(encoding='utf-8'))
                return
            except (OSError, UnicodeError):
                pass
        observed.opaque = True
    elif event in ('os.system', 'os.posix_spawn', 'os.exec', 'os.fork', 'ctypes.dlopen'):
        observed.opaque = True


@contextmanager
def observe(root, observed):
    global _active, _installed
    if not _installed:
        sys.addaudithook(_audit)
        _installed = True
    previous = _active
    _active = root, observed
    try:
        yield
    finally:
        _active = previous


def project_imports(source):
    """Recognize ordinary project/Mathlib import declarations; otherwise use all Lean."""
    result = set()
    if re.search(r'\bIO\.|\b(include_str|run_cmd|initialize|unsafe|elab|macro|run_tac)\b|#eval', source):
        return None
    for line in source.splitlines():
        if not re.search(r'\bimport\b', line):
            continue
        match = re.fullmatch(r'\s*import\s+([A-Za-z0-9_.\s]+?)(?:\s*--.*)?', line)
        if not match:
            return None
        modules = match.group(1).split()
        for module in modules:
            if module.split('.')[0] == 'PrimeFactors':
                result.add(module.replace('.', '/')+'.lean')
            elif module.split('.')[0] not in ('Mathlib','Lean','Std','Init','Batteries','Aesop','Qq'):
                return None
    return result


@lru_cache(maxsize=2048)
def module_imports(file, content_hash):
    return project_imports(file.read_text(encoding='utf-8'))


def dependencies(inputs, method, sources, startup, local):
    opaque = local.opaque or startup.opaque
    isolated = method in ISOLATED and not opaque
    fixture_reads = startup.fixtures | local.fixtures
    broad = dict(fixture_tree=inputs.fixture_tree, lean_tree=inputs.lean_tree,
                 other_tree=inputs.other_tree)
    if opaque:
        return broad
    # Directory membership covers existence/stat checks even if a failed lookup
    # did not issue an open. Each actually read file is hashed separately.
    deps = dict(fixtures={name: inputs.fixtures.get(name) for name in fixture_reads})
    if not isolated:
        deps['fixture_names'] = inputs.fixture_names
    deps['other'] = {name: inputs.other.get(name) for name in startup.other | local.other}
    todo = set(startup.lean | local.lean)
    for source in set(sources.values()) | local.headers | startup.headers:
        imports = project_imports(source)
        if imports is None:
            return broad
        todo.update(imports)
    closure = {}
    while todo:
        name = todo.pop()
        if name in closure:
            continue
        if name not in inputs.lean:
            return broad
        closure[name] = inputs.lean[name]
        imports = module_imports(inputs.root/name, closure[name])
        if imports is None:
            return broad
        todo.update(imports)
    deps['lean'] = closure
    return deps


def compatible(inputs, deps):
    if not isinstance(deps, dict):
        return False
    if set(deps) == {'fixture_tree', 'lean_tree', 'other_tree'}:
        return deps == dict(fixture_tree=inputs.fixture_tree, lean_tree=inputs.lean_tree,
                            other_tree=inputs.other_tree)
    if set(deps) not in ({'fixtures','lean','other'}, {'fixtures','lean','other','fixture_names'}):
        return False
    return (deps.get('fixture_names', inputs.fixture_names) == inputs.fixture_names and
            all(inputs.fixtures.get(k) == v for k,v in deps['fixtures'].items()) and
            all(inputs.other.get(k) == v for k,v in deps['other'].items()) and
            all(k in inputs.lean and inputs.lean[k] == v for k,v in deps['lean'].items()))


def proof_references(node):
    if isinstance(node, dict):
        for value in node.values():
            yield from proof_references(value)
    elif isinstance(node, list):
        for value in node:
            yield from proof_references(value)
    elif isinstance(node, str) and node.startswith('proofs/'):
        yield node[len('proofs/'):]


def validate(row, case, method, sources):
    if (not isinstance(row, dict) or row.get('id') != case['id'] or
            row.get('method') != method or
            any(k not in row or row[k] != case[k] for k in ('n', 'factors', 'remaining', 'status'))):
        raise ValueError('row and benchmark fixture disagree')
    if (not isinstance(row.get('measurement'), dict) or
            any(k not in row['measurement'] for k in PROVENANCE)):
        raise ValueError('missing benchmark measurement provenance')
    record = row['measurement']
    if (not isinstance(record['commit'], str) or not re.fullmatch('[0-9a-f]{40,64}', record['commit'])
            or not isinstance(record['measured_at'], str)
            or datetime.fromisoformat(record['measured_at']).tzinfo is None
            or any(not isinstance(record[k], str) for k in ('repository', 'platform', 'cpu', 'python', 'lean'))
            or (record['run_id'] is not None and not str(record['run_id']).isdigit())):
        raise ValueError('invalid benchmark measurement provenance')
    complete = case['status'] == 'complete'
    expected = f"proofs/{case['id']}.lean" if complete else None
    if row.get('verified') is not complete or row.get('certificate') != expected:
        raise ValueError('benchmark certificate status mismatch')
    if (not isinstance(sources, dict) or
            any(not PROOF_NAME.fullmatch(name) or not isinstance(value, str)
                for name, value in sources.items()) or
            any(name not in sources for name in proof_references(row))):
        raise ValueError('invalid or missing generated proof source')


def collect_proofs(directory):
    sources = {}
    for file in directory.iterdir():
        if file.is_symlink() or not file.is_file() or not PROOF_NAME.fullmatch(file.name):
            raise ValueError(f'unexpected generated artifact: {file.name}')
        sources[file.name] = file.read_bytes().decode('utf-8')
    return sources


def read_entry(directory, key, case, method, inputs):
    """Treat damaged, incomplete and incompatible entries as ordinary cache misses."""
    try:
        saved = json.loads((directory / (case['id'] + '.json')).read_bytes())
        payload = saved['payload']
        if payload['key'] != key or saved['sha256'] != digest(encoded(payload)):
            return None
        if not compatible(inputs, payload['dependencies']):
            return None
        row = payload['row']
        sources = payload['proofs']
        if payload['proof_hashes'] != {name: digest(value.encode('utf-8'))
                                       for name, value in sources.items()}:
            return None
        validate(row, case, method, sources)
        return row, sources
    except (OSError, ValueError, AttributeError, KeyError, TypeError, RecursionError):
        return None


def write_entry(directory, key, row, sources, deps):
    payload = dict(key=key, dependencies=deps, row=row, proofs=sources, proof_hashes={
        name: digest(value.encode('utf-8')) for name, value in sources.items()})
    directory.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(dir=directory, delete=False) as tmp:
        path = Path(tmp.name)
        try:
            tmp.write(encoded(dict(sha256=digest(encoded(payload)), payload=payload)))
        except BaseException:
            path.unlink(missing_ok=True)
            raise
    try:
        os.replace(path, directory / (row['id'] + '.json'))
    finally:
        path.unlink(missing_ok=True)


def run_cases(cases, run_case, proofs, scratch, provenance, inputs=None, cache=None, startup=None):
    """Assemble isolated case outputs in a fresh directory. Cache misses are staged."""
    startup = startup or Observed()
    rows = []
    keys = []
    names = set()
    hits = 0
    # A later case may consult a memoized loader previously populated by another
    # case in this process. Carry forward the non-code files those loaders read.
    inherited = Observed()
    for filename, method, case in cases:
        name = case['id']
        if not CASE_ID.fullmatch(name) or name in names:
            raise ValueError(f'duplicate or invalid benchmark ID: {name!r}')
        names.add(name)
        key = case_key(inputs, filename, method, case) if cache is not None else None
        saved = read_entry(cache, key, case, method, inputs) if key else None
        if saved is None:
            with tempfile.TemporaryDirectory(dir=scratch) as tmp:
                directory = Path(tmp)
                if key:
                    local = Observed()
                    with observe(inputs.root, local):
                        row = run_case(case, method, directory)
                else:
                    row = run_case(case, method, directory)
                row['measurement'] = dict(provenance, measured_at=timestamp())
                sources = collect_proofs(directory)
            validate(row, case, method, sources)
            if key:
                if method not in ISOLATED:
                    local.fixtures.update(inherited.fixtures)
                    local.lean.update(inherited.lean)
                    local.other.update(inherited.other)
                inherited.fixtures.update(local.fixtures)
                inherited.lean.update(local.lean)
                inherited.other.update(local.other)
                deps = dependencies(inputs, method, sources, startup, local)
                write_entry(scratch / 'entries', key, row, sources, deps)
                keys.append(name)
        else:
            row, sources = saved
            hits += 1
        for leaf, source in sources.items():
            # An overlap between primary and secondary proof names is an error.
            with (proofs / leaf).open('xb') as out:
                out.write(source.encode('utf-8'))
        row['reused'] = saved is not None
        rows.append(row)
        action = 'reused' if saved is not None else f"{row['wall_seconds']:.3f}s"
        print(f"{name}  {row['status']}  {action}", flush=True)
    return rows, hits, keys


def timestamp():
    return datetime.now(timezone.utc).isoformat(timespec='seconds')


def runtime_key():
    try:
        gmpy = version('gmpy2')
    except PackageNotFoundError:
        gmpy = None
    return dict(python=sys.version, python_implementation=sys.implementation.name,
                platform=platform.platform(), arch=platform.machine(), gmpy2=gmpy,
                lean=subprocess.check_output(['lean', '--version'], text=True).strip(),
                lake=subprocess.check_output(['lake', '--version'], text=True).strip(),
                environment={name: os.environ.get(name) for name in
                             ('ImageOS', 'ImageVersion', 'ELAN_TOOLCHAIN', 'LEAN_SYSROOT',
                              'LEAN_PATH', 'LEAN_SRC_PATH', 'PYTHONPATH', 'PYTHONHASHSEED',
                              'PRIME_FACTORS_CERTIFICATE_CONTEXT')})


def clean_packages(root):
    """A version pin identifies sources only for unmodified dependency checkouts."""
    if os.getenv('LEAN_PATH') or os.getenv('LEAN_SRC_PATH'):
        return False
    manifest = json.loads((root/'lake-manifest.json').read_text())
    for dep in manifest['packages']:
        directory = root / manifest['packagesDir'] / dep['name']
        if dep['type'] != 'git' or not (directory / '.git').exists():
            return False
        rev = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=directory, text=True)
        changes = subprocess.check_output(['git', '--no-optional-locks', 'status', '--porcelain'],
                                          cwd=directory)
        if rev.strip() != dep['rev'] or changes:
            return False
    return True


def publish_entries(staged, keys, directory):
    """Copy via a destination-local tempfile, including across different disks."""
    if not keys:
        return
    directory.mkdir(parents=True, exist_ok=True)
    for key in keys:
        target = directory / f'{key}.json'
        with tempfile.NamedTemporaryFile(dir=directory, delete=False) as tmp:
            path = Path(tmp.name)
            try:
                with (staged / target.name).open('rb') as source:
                    shutil.copyfileobj(source, tmp)
            except BaseException:
                path.unlink(missing_ok=True)
                raise
        try:
            os.replace(path, target)
        finally:
            path.unlink(missing_ok=True)


@contextmanager
def output_lock(out):
    """Serialize replacements, using a lock outside the published site."""
    lock = Path(tempfile.gettempdir()) / ('prime-factors-benchmark-' + digest(os.fsencode(out)) + '.lock')
    with lock.open('a+b') as handle:
        if os.name == 'nt':
            import msvcrt
            if handle.seek(0, os.SEEK_END) == 0:
                handle.write(b'0')
                handle.flush()
            handle.seek(0)
            msvcrt.locking(handle.fileno(), msvcrt.LK_LOCK, 1)
        else:
            import fcntl
            fcntl.flock(handle, fcntl.LOCK_EX)
        yield


def publish_site(staged, out, standalone=()):
    """Install the new proof set and results together after every case succeeds."""
    with output_lock(out):
        proofs = out / 'proofs'
        old = staged / 'previous-proofs'
        if proofs.is_symlink():
            raise ValueError('refusing to replace a symlinked proof directory')
        if proofs.exists():
            for name in standalone:
                source = proofs / name
                if source.is_file() and not source.is_symlink():
                    with (staged / 'proofs' / name).open('xb') as target, source.open('rb') as stream:
                        shutil.copyfileobj(stream, target)
            proofs.rename(old)
        try:
            (staged/'proofs').rename(proofs)
            (staged/'results.json').replace(out/'results.json')
        except BaseException:
            if proofs.exists():
                proofs.rename(staged/'proofs')
            if old.exists():
                old.rename(proofs)
            raise
