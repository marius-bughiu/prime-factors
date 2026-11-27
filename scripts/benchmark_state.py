"""Content-addressed benchmark rows and the exact proof sources produced with them."""

import ast
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


# These methods use no memoized data loaders from earlier cases.
ISOLATED = frozenset(('fermat', 'high-word-sum-ranking', 'high-word-suffix-ranking', 'fractional-word-ranking'))
CASE_ID = re.compile(r'[A-Za-z0-9_-]+')
PROOF_NAME = re.compile(r'[A-Za-z0-9_-]+\.lean')
FORMAT = 'benchmark-rows-v2'
PROVENANCE = ('commit', 'measured_at', 'run_id', 'repository', 'platform', 'cpu', 'python', 'lean')


def encoded(value):
    return json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(',', ':'),
                      allow_nan=False).encode('utf-8')


def digest(data):
    return hashlib.sha256(data).hexdigest()


def presentation(name):
    return (Path(name).parts[0] in ('site', 'discoveries', 'docs', 'tests', '.github') or
            name in ('README.md', 'LICENSE', 'CONTRIBUTING.md', 'AGENTS.md', 'scripts/render_site.py',
                     'scripts/pages_revision.py', 'scripts/ci_lean_build.py', 'scripts/verify_checks.py',
                     'scripts/verification_registry.py'))


class Inputs:
    def __init__(self, root, shared, fixtures, lean, other=None, python=(), guard=None,
                 files=(), child_known=False, lean_probes=()):
        self.root = root
        self.shared = shared
        self.fixtures = fixtures
        self.lean = lean
        self.other = other or {}
        self.other_tree = digest(encoded(self.other))
        self.python = frozenset(python)
        self.guard = guard
        self.files = frozenset(files) | self.fixtures.keys() | self.lean.keys() | self.other.keys()
        self.child_known = child_known
        self.lean_probes = frozenset(lean_probes)
        self.fixture_tree = digest(encoded(fixtures))
        self.lean_tree = digest(encoded(lean))

    def snapshot(self):
        return self.shared, self.fixture_tree, self.lean_tree, self.other_tree


def flat_experiment(name):
    parts = Path(name).parts
    return len(parts) == 2 and parts[0] == 'experiments' and parts[1].endswith('.py')


# File opens and directory enumeration have Python audit events. Metadata probes, native
# filesystem APIs and dynamic imports can take paths which those events do not describe.
# If reachable code introduces one, leave rows uncached until its inputs are accounted for.
UNOBSERVED = frozenset(('exists', 'lexists', 'is_file', 'is_dir', 'isfile', 'isdir',
    'stat', 'lstat', 'fstat', 'statvfs', 'access', 'is_symlink', 'islink', 'is_mount', 'ismount',
    'is_socket', 'is_fifo', 'is_block_device', 'is_char_device', 'isjunction', 'is_junction',
    'getsize', 'getmtime', 'getctime', 'getatime', 'readlink', 'samefile', 'find_spec',
    'spec_from_file_location', 'import_module', 'run_path', 'run_module', 'load_module',
    'exec_module', 'get_data', '__import__', 'exec', 'eval'))


# The audit hook lives in the parent Python interpreter. Only these reviewed child
# programs have fixed inputs that the parent can reconstruct. New child code executes
# normally and stays fresh until its I/O contract is reviewed.
FACTOR_HELPERS = {
    'experiments/subgroup_split.py': 'dccb6ceafb7a2c58415cef29ff8f2bdeaf4fae07850cce259f1fbbb540076c47',
    'scripts/factor.py': '019e650950423856c6458a893a44759201dac367dac85f705d9e9520d9dd7d42',
    'scripts/certificate_cache.py': '49f95d43eac2780214b239b01b5d06d7c2e236ffff5faaa4fa8f0bbbce1bf650',
}
LEAN_PROBES = {
    'experiments/ReducedOrders.lean': ('601d3b231b50465afb75070e58857c99d8b9a4704d87be0604f200d82b4ed521', ()),
    'experiments/GroupedNormProbe.lean': ('6870ab8be1127d99107c773121b5913b405eea7a2926873d1a7ecef959e252d6',
                                         ('PrimeFactors/GroupedNormFactors.lean',)),
}


def import_nodes(tree, entrypoint):
    pending = [tree]
    while pending:
        node = pending.pop()
        yield node
        if (not entrypoint and isinstance(node, ast.If) and
                ast.unparse(node.test) in ("__name__ == '__main__'", "'__main__' == __name__")):
            pending.extend(node.orelse)
        else:
            pending.extend(ast.iter_child_nodes(node))


@lru_cache(maxsize=1024)
def python_references(path, name, content_hash):
    """Static imports include lazy branches and every package initializer on their path."""
    tree = ast.parse(path.read_bytes(), filename=str(path))
    package = name.split('/')[:-1]
    modules = set()
    unknown = None
    for node in import_nodes(tree, name in ('scripts/benchmark.py', 'scripts/factor.py')):
        if isinstance(node, ast.Import):
            imports = [item.name for item in node.names]
        elif isinstance(node, ast.ImportFrom):
            if node.level > len(package):
                return (), f'{name}:{node.lineno} unresolved relative import'
            prefix = package[:len(package)-node.level+1] if node.level else []
            if node.module:
                prefix.extend(node.module.split('.'))
            base = '.'.join(prefix)
            imports = [base, *('.'.join([*prefix, item.name]) for item in node.names)]
        else:
            imports = []
        for module in imports:
            parts = module.split('.')
            # The repository root and scripts directory are routinely on sys.path. Some
            # embeddings also expose experiments directly: account for a newly shadowing
            # flat module even when the original import resolved to the standard library.
            for i in range(1, len(parts)+1):
                prefix = '/'.join(parts[:i])
                modules.add(prefix)
                if not isinstance(node, ast.ImportFrom) or not node.level:
                    modules.update(('experiments/'+prefix, 'scripts/'+prefix))
            if (parts[0] in ('ctypes', 'cffi', 'runpy', 'importlib', 'posix', 'nt', 'pkgutil') or
                    parts[-1] in UNOBSERVED or (parts[0] in ('os', 'pathlib') and parts[-1] == '*')):
                unknown = f'{name}:{node.lineno} {module}'
        if isinstance(node, ast.Attribute) and node.attr in UNOBSERVED:
            unknown = f'{name}:{node.lineno} {node.attr}'
        if isinstance(node, ast.Name) and node.id in ('__import__', 'exec', 'eval'):
            unknown = f'{name}:{node.lineno} {node.id}'
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute) and node.func.attr == 'resolve':
            if (ast.unparse(node) != 'Path(__file__).resolve()' and
                    FACTOR_HELPERS.get(name) != content_hash):
                unknown = f'{name}:{node.lineno} path resolution'
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == 'getattr':
            obj = node.args[0] if node.args else None
            attr = node.args[1] if len(node.args) > 1 else None
            if ((isinstance(obj, ast.Name) and obj.id in ('os', 'sys', 'Path', 'pathlib', 'importlib')) or
                    (isinstance(attr, ast.Constant) and attr.value in UNOBSERVED)):
                unknown = f'{name}:{node.lineno} dynamic lookup'
    return modules, unknown


def python_inputs(root, files, roots=('scripts/benchmark.py', 'scripts/factor.py')):
    """Only flat experiment modules can be omitted from the shared code key."""
    pending = list(roots)
    seen = set()
    guard = None
    while pending:
        name = pending.pop()
        if name in seen or name not in files:
            continue
        seen.add(name)
        # This verifier is itself shared. Its implementation reads repository/cache
        # metadata by design, outside the calculation producing a benchmark result.
        if name == 'scripts/benchmark_state.py':
            continue
        try:
            modules, unknown = python_references(root/name, name, files[name])
        except (SyntaxError, OSError, UnicodeError) as error:
            return seen, f'cannot resolve {name}: {error}'
        if unknown:
            guard = unknown
        for module in modules:
            pending.extend((module+'.py', module+'/__init__.py'))
    return seen, guard


def output_path(path):
    return path.resolve()


def standalone_proofs():
    # Publication happens after measurement. This registry does not compute benchmark rows.
    from scripts.verify_checks import CHECKS
    return {name for check in CHECKS for name in check.outputs}


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
    all_python = {name: value for collection in (shared, other) for name, value in collection.items()
                  if name.endswith('.py')}
    reachable, guard = python_inputs(root, all_python)
    child, _ = python_inputs(root, all_python, ('scripts/factor.py',))
    child_known = {name: all_python[name] for name in child} == FACTOR_HELPERS
    known_probes = {name for name, (fingerprint, _) in LEAN_PROBES.items() if shared.get(name) == fingerprint}
    for name in reachable & other.keys():
        shared[name] = other.pop(name)
    for name in list(shared):
        if flat_experiment(name) and name not in reachable:
            other[name] = shared.pop(name)
    return Inputs(root, digest(encoded([FORMAT, runtime, shared])), fixtures, lean, other,
                  reachable, guard, shared.keys(), child_known, known_probes)


def case_key(inputs, filename, method, case):
    return digest(encoded([inputs.shared, filename, method, case]))


# The runner is serial. Observe imports before eager experiment imports and attach
# their fixture reads to every row. No hook executes code from a restored entry.
_active = None
_installed = False


class Observed:
    def __init__(self, outputs=None):
        self.outputs = outputs
        self.reads = set()
        self.processes = set()
        self.unsafe = False
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
            if event != 'open':
                observed.unsafe = True
            return
        path = os.fsdecode(path)
        file = Path(os.path.abspath(path))
        if not file.is_relative_to(root):
            return
        if observed.outputs is not None and file.is_relative_to(observed.outputs):
            return
        name = file.relative_to(root).as_posix()
        if event == 'open':
            caller = sys._getframe(1)
            bytecode = ('__pycache__' in file.parts and caller.f_globals.get('__name__') in
                        ('_frozen_importlib_external', 'importlib._bootstrap_external'))
            if not bytecode:
                observed.reads.add(name)
        if event != 'open':
            # Importlib's name lookup is accounted for by the static closure, including
            # packages that can shadow a flat module. User enumeration observes every name.
            caller = sys._getframe(1)
            import_scan = (caller.f_code.co_name == '_fill_cache' and
                           caller.f_globals.get('__name__') in
                           ('_frozen_importlib_external', 'importlib._bootstrap_external'))
            if not import_scan:
                observed.unsafe = True
        elif file.parent == root/'benchmarks' and file.suffix == '.json':
            observed.fixtures.add(name)
        elif name == 'PrimeFactors.lean' or (name.startswith('PrimeFactors/') and file.suffix == '.lean'):
            observed.lean.add(name)
        elif (presentation(name) or flat_experiment(name)) and '__pycache__' not in file.parts:
            observed.other.add(name)
    elif event in ('pathlib.Path.glob', 'pathlib.Path.rglob', 'glob.glob', 'glob.glob/2', 'os.walk', 'os.fwalk'):
        # Some glob implementations can return no matches before issuing a directory read.
        observed.unsafe = True
    elif event == 'subprocess.Popen':
        _, args, cwd, _ = args
        if not isinstance(args, (list, tuple)):
            observed.unsafe = True
            return
        args = [os.fsdecode(arg) for arg in args]
        if (len(args) >= 2 and args[0] == sys.executable and
                Path(cwd or Path.cwd()).resolve() == root and args[1] == 'scripts/factor.py' and
                '--verify' in args):
            # This audited CLI only reads canonical certificate modules if it finds factors;
            # the retained generated source supplies their actual imports.
            observed.processes.add('scripts/factor.py')
            observed.lean.add('PrimeFactors/Certificate.lean')
            return
        if (len(args) >= 5 and args[:4] == ['lake', 'env', 'lean', '--run'] and
                args[4] in LEAN_PROBES and Path(cwd or Path.cwd()).resolve() == root):
            observed.processes.add(args[4])
            observed.lean.update(LEAN_PROBES[args[4]][1])
            return
        if len(args) == 5 and args[:4] == ['lake', 'env', 'lean', '-DwarningAsError=true']:
            try:
                source = Path(cwd or Path.cwd()) / args[4]
                observed.headers.add(source.read_text(encoding='utf-8'))
                return
            except (OSError, UnicodeError):
                pass
        observed.unsafe = True
    elif event in ('os.system', 'os.posix_spawn', 'os.exec', 'os.fork', 'ctypes.dlopen'):
        observed.unsafe = True


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
    """Recognize ordinary pinned imports. Arbitrary Lean metaprograms can read hidden inputs."""
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
    processes = startup.processes | local.processes
    if (startup.unsafe or local.unsafe or
            ('scripts/factor.py' in processes and not inputs.child_known) or
            (processes - {'scripts/factor.py'} - inputs.lean_probes)):
        return None
    missing = sorted((startup.reads | local.reads) - inputs.files)
    # Ignored inputs, such as build/table.json, have no trusted content fingerprint.
    # An absent name can be reused only while the path continues to be absent.
    if any(os.path.lexists(inputs.root / name) for name in missing):
        return None
    opaque = local.opaque or startup.opaque or bool(processes & inputs.lean_probes)
    fixture_reads = startup.fixtures | local.fixtures
    broad = dict(fixture_tree=inputs.fixture_tree, lean_tree=inputs.lean_tree,
                 other_tree=inputs.other_tree)
    if missing:
        broad['missing'] = missing
    # A failed open records an absent path with value None. Its later creation invalidates
    # that row, while opening an unrelated experiment does not affect the shared key.
    deps = dict(fixtures={name: inputs.fixtures.get(name) for name in fixture_reads})
    deps['other'] = {name: inputs.other.get(name) for name in (startup.other | local.other) - inputs.python}
    todo = set(startup.lean | local.lean)
    for source in set(sources.values()) | local.headers | startup.headers:
        imports = project_imports(source)
        if imports is None:
            return None
        todo.update(imports)
    closure = {}
    while todo:
        name = todo.pop()
        if name in closure:
            continue
        if name not in inputs.lean:
            return None
        closure[name] = inputs.lean[name]
        imports = module_imports(inputs.root/name, closure[name])
        if imports is None:
            return None
        todo.update(imports)
    if opaque:
        return broad
    deps['lean'] = closure
    if missing:
        deps['missing'] = missing
    return deps


def compatible(inputs, deps):
    if inputs.guard or not isinstance(deps, dict):
        return False
    deps = dict(deps)
    for name in deps.pop('missing', ()):
        path = Path(name)
        if path.is_absolute() or '..' in path.parts or os.path.lexists(inputs.root/path):
            return False
    if set(deps) == {'fixture_tree', 'lean_tree', 'other_tree'}:
        return deps == dict(fixture_tree=inputs.fixture_tree, lean_tree=inputs.lean_tree,
                            other_tree=inputs.other_tree)
    if set(deps) != {'fixtures','lean','other'}:
        return False
    return (all(inputs.fixtures.get(k) == v for k,v in deps['fixtures'].items()) and
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
        key = case_key(inputs, filename, method, case) if cache is not None and not inputs.guard else None
        can_restore = key and not (method not in ISOLATED and (inherited.unsafe or inherited.opaque))
        saved = read_entry(cache, key, case, method, inputs) if can_restore else None
        if saved is None:
            with tempfile.TemporaryDirectory(dir=scratch) as tmp:
                directory = Path(tmp)
                if key:
                    local = Observed(directory)
                    with observe(inputs.root, local):
                        row = run_case(case, method, directory)
                else:
                    row = run_case(case, method, directory)
                row['measurement'] = dict(provenance, measured_at=timestamp())
                sources = collect_proofs(directory)
            validate(row, case, method, sources)
            if key:
                if method not in ISOLATED:
                    local.unsafe |= inherited.unsafe
                    local.opaque |= inherited.opaque
                    local.reads.update(inherited.reads)
                    local.fixtures.update(inherited.fixtures)
                    local.lean.update(inherited.lean)
                    local.other.update(inherited.other)
                inherited.reads.update(local.reads)
                inherited.unsafe |= local.unsafe
                inherited.opaque |= local.opaque
                inherited.fixtures.update(local.fixtures)
                inherited.lean.update(local.lean)
                inherited.other.update(local.other)
                deps = dependencies(inputs, method, sources, startup, local)
                if deps is not None:
                    write_entry(scratch / 'entries', key, row, sources, deps)
                    keys.append(name)
                else:
                    inherited.unsafe = True
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
