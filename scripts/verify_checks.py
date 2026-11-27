"""Run independent verification commands and reuse complete records from a trusted cache."""

import argparse
import ast
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts import benchmark_state
from scripts.verification_registry import CHECKS, RESEARCH, Check, experiment

PINS = ('lean-toolchain', 'lakefile.toml', 'lake-manifest.json', 'scripts/fetch-cache.sh',
        'scripts/benchmark_state.py')
OMIT = {'.git', '.lake', 'build', '__pycache__', '.venv', 'venv', '.DS_Store'}
SCHEMA = 1

# This exact --check driver kernel-checks two generated sources and compares their
# hashes with the fixture. On a successful run we inspected both sources using
# benchmark_state.project_imports. The Python digest below covers local_imports
# of the driver, using the same (relative path, SHA-256) entries as a normal key.
# Re-review both source headers and the driver closure before changing these pins.
NEGATIVE_MENU = experiment('negative_menu_control', '--check',
                           data=('research/negative-menu-control.json',), lean=True)
NEGATIVE_DRIVER = '4d1e329b011c9445dcbda69a1579921ce1abb5f4ffa2e6d01b81fd833a2fbd3b'
NEGATIVE_PROOFS = {
    'Factor': '2a5ce0c5118c5cb90874a42b9b960e99dc0324a5c47e76583c8dd13d37532201',
    'Obstruction': '81284398d3aa0304dd95b7ef50ce48522a9df2d9e4f33307c7b398b53854d7c7',
}
NEGATIVE_ROOTS = ('PrimeFactors/Certificate.lean', 'PrimeFactors/PartialOrder.lean',
                  'PrimeFactors/NegativeTargetObstruction.lean')


def digest(data):
    return hashlib.sha256(data).hexdigest()


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':')).encode('utf-8')


def walk_files(path, ignored=None):
    if path == ignored:
        return
    if path.is_dir():
        for child in sorted(path.iterdir()):
            if child.name not in OMIT and not child.name.startswith('.') and child.suffix != '.pyc':
                yield from walk_files(child, ignored)
    elif path.is_file():
        yield path


class UntrackedProcess(Exception):
    """A checker delegates work to a program with unknown inputs."""


def local_imports(root, filename):
    """Include transitive local imports even from conditional paths. Unknown loading widens scope."""
    seen = set()
    pending = [filename]
    while pending:
        path = pending.pop()
        if path in seen:
            continue
        seen.add(path)
        tree = ast.parse(path.read_bytes(), filename=str(path))
        prover_helper = path.relative_to(root).as_posix() in (
            'scripts/factor.py', 'scripts/certificate_cache.py')
        for node in ast.walk(tree):
            if not prover_helper and (
                    isinstance(node, ast.Import) and any(a.name == 'subprocess' for a in node.names)
                    or isinstance(node, ast.ImportFrom) and node.module == 'subprocess'):
                raise UntrackedProcess(path.relative_to(root))
            if isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute):
                if (isinstance(node.func.value, ast.Name) and node.func.value.id == 'os'
                        and node.func.attr in ('system', 'popen', 'posix_spawn', 'posix_spawnp')):
                    raise UntrackedProcess(path.relative_to(root))
                if prover_helper and isinstance(node.func.value, ast.Name) and node.func.value.id == 'subprocess':
                    args = node.args[0] if node.args else None
                    argv = [a.value if isinstance(a, ast.Constant) else None for a in args.elts] \
                        if isinstance(args, (ast.List, ast.Tuple)) else []
                    # These two commands only annotate a certificate that already passed the kernel.
                    provenance = (path.name == 'certificate_cache.py' and node.func.attr == 'check_output'
                                  and len(node.args) == 1 and all(k.arg in ('cwd', 'text') for k in node.keywords)
                                  and argv in (['git', 'rev-parse', 'HEAD'], ['git', 'status', '--porcelain']))
                    if argv[:3] != ['lake', 'env', 'lean'] and not provenance:
                        raise UntrackedProcess(path.relative_to(root))
            if isinstance(node, ast.Call) and (
                    isinstance(node.func, ast.Name) and node.func.id in ('__import__', 'exec', 'eval') or
                    isinstance(node.func, ast.Attribute) and node.func.attr in
                    ('import_module', 'spec_from_file_location', 'run_path', 'run_module')):
                return None
            if isinstance(node, ast.Import):
                names = [item.name for item in node.names]
            elif isinstance(node, ast.ImportFrom):
                package = list(path.relative_to(root).parts[:-1])
                if node.level:
                    package = package[:len(package) - node.level + 1]
                    prefix = '.'.join(package + ([node.module] if node.module else []))
                else:
                    prefix = node.module or ''
                names = [prefix, *(f'{prefix}.{item.name}' for item in node.names)]
            else:
                continue
            for name in names:
                parts = name.split('.')
                if parts[0] not in ('experiments', 'scripts'):
                    continue
                for i in range(1, len(parts) + 1):
                    p = root.joinpath(*parts[:i])
                    for candidate in (p.with_suffix('.py'), p/'__init__.py'):
                        if candidate.is_file() and candidate not in seen:
                            pending.append(candidate)
    return seen


class Inputs:
    def __init__(self, root, cache=None):
        self.root = root
        self.ignored = (cache/'checks').resolve() if cache is not None else None
        self.hashes = {}
        self.groups = {}

    def group(self, spec):
        if spec not in self.groups:
            path = self.root/spec
            self.groups[spec] = tuple(walk_files(path, self.ignored)) if path.is_dir() else (path,)
        return self.groups[spec]

    def entries(self, files):
        entries = []
        for path in sorted(files):
            if path not in self.hashes:
                self.hashes[path] = digest(path.read_bytes()) if path.is_file() else None
            entries.append((path.relative_to(self.root).as_posix(), self.hashes[path]))
        return entries

    def lean_sources(self, check, python):
        """Follow only checked source roots. All other recipes retain the full library."""
        broad = {*self.group('PrimeFactors'), self.root/'PrimeFactors.lean'}
        if len(check.command) == 4 and check.command[:3] == ('lake', 'env', 'lean'):
            name = check.command[3]
            path = Path(name)
            if (name not in check.data or name.startswith('-') or path.suffix != '.lean'
                    or path.is_absolute() or '..' in path.parts):
                return broad
            todo = [path]
        elif check == NEGATIVE_MENU and python and digest(canonical(self.entries(python))) == NEGATIVE_DRIVER:
            try:
                receipt = json.loads((self.root/check.data[0]).read_bytes())
            except (OSError, ValueError, UnicodeError):
                return broad
            if not isinstance(receipt, dict) or receipt.get('lean_source_sha256') != NEGATIVE_PROOFS:
                return broad
            todo = [Path(name) for name in NEGATIVE_ROOTS]
        else:
            return broad
        files = set()
        while todo:
            path = self.root/todo.pop()
            if path in files:
                continue
            if not path.is_file():
                return broad
            if path.resolve() != self.root.resolve()/path.relative_to(self.root):
                raise UntrackedProcess(path.relative_to(self.root))
            files.add(path)
            imports = benchmark_state.project_imports(path.read_text(encoding='utf-8'))
            if imports is None:
                # A metaprogram can read inputs beyond even the whole Lean source tree.
                raise UntrackedProcess(path.relative_to(self.root))
            todo.extend(Path(name) for name in imports)
        return files

    def fingerprint(self, check, environment):
        root = self.root
        files = {root/'scripts/verify_checks.py', *(root/p for p in PINS)}
        if check.name == 'unit-tests':
            # Tests invoke subprocesses, discover new files and read many parts of the checkout.
            files.update(self.group('.'))
            files.update(self.group('.github'))
        else:
            for spec in check.data:
                files.update(self.group(spec))
            sources = None
            if check.command[:2] == ('python3', '-m'):
                name = check.command[2].replace('.', '/') + '.py'
                sources = local_imports(root, root/name)
                if sources is None:
                    # Dynamic module loading may use local resources outside the two Python packages.
                    files.update(self.group('.'))
                    files.update(self.group('.github'))
                else:
                    files.update(sources)
            if check.lean:
                files.update(self.lean_sources(check, sources))
        # A command's expanded specification includes every setting it takes from the
        # registry. Registering a separate receipt does not change this specification.
        specification = (check.name, check.command, check.data, check.lean, check.outputs)
        return digest(canonical([SCHEMA, specification, environment, self.entries(files)]))


def load_outputs(path, check, key):
    try:
        record = json.loads(path.read_text())
        if record['schema'] != SCHEMA or record['fingerprint'] != key or record['status'] != 'success':
            return None
        outputs = record['outputs']
        if set(outputs) != set(check.outputs):
            return None
        for output in outputs.values():
            if digest(output['source'].encode('utf-8')) != output['sha256']:
                return None
        return outputs
    except (OSError, ValueError, KeyError, TypeError, AttributeError, UnicodeError):
        return None


def atomic_write(path, data, *, public=False):
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(dir=path.parent, delete=False) as file:
        temp = Path(file.name)
        try:
            file.write(data)
            file.close()
            if public:
                temp.chmod(0o644)
            os.replace(temp, path)
        finally:
            temp.unlink(missing_ok=True)


def run(check, inputs, environment, cache, execute=subprocess.run):
    root = inputs.root
    if cache is None:
        execute(check.command, cwd=root, check=True)
        return 'ran'
    try:
        key = inputs.fingerprint(check, environment)
    except UntrackedProcess as error:
        print(f'  Running in full because {error} may use untracked inputs.', flush=True)
        execute(check.command, cwd=root, check=True)
        return 'ran'
    record = cache/'checks'/(check.name + '.json')
    proofs = root/'build/site/proofs'
    outputs = load_outputs(record, check, key)
    if outputs is not None:
        for name, output in outputs.items():
            atomic_write(proofs/name, output['source'].encode('utf-8'), public=True)
        return 'reused'

    # Old files cannot stand in for outputs a successful command was expected to generate.
    for name in check.outputs:
        (proofs/name).unlink(missing_ok=True)
    execute(check.command, cwd=root, check=True)
    outputs = {}
    for name in check.outputs:
        data = (proofs/name).read_bytes()
        outputs[name] = dict(source=data.decode('utf-8'), sha256=digest(data))
    if Inputs(root, cache).fingerprint(check, environment) != key:
        raise RuntimeError(f'{check.name}: verification inputs changed during the check')
    atomic_write(record, canonical(dict(schema=SCHEMA, fingerprint=key, status='success', outputs=outputs)))
    return 'ran'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cache-dir', type=Path, help='trusted verification state, optional')
    parser.add_argument('--group', choices=('all', 'tests', 'receipts'), default='all')
    parser.add_argument('--only', choices=[c.name for c in CHECKS], action='append',
                        help='limit this invocation to named checks (repeatable)')
    parser.add_argument('--list', action='store_true')
    args = parser.parse_args()
    checks = [c for c in CHECKS if args.group == 'all' or (args.group == 'tests') == (c.name == 'unit-tests')]
    if args.only:
        checks = [c for c in checks if c.name in args.only]
        if len(checks) != len(set(args.only)):
            parser.error('--only names must belong to the selected group')
    cached = args.cache_dir is not None and not args.list
    environment = None
    if cached:
        try:
            environment = benchmark_state.runtime_key()
            environment['PYTHONOPTIMIZE'] = os.environ.get('PYTHONOPTIMIZE')
        except (OSError, ValueError, subprocess.CalledProcessError) as error:
            print(f'Cannot establish the cache runtime; checks will run in full: {error}', flush=True)
            cached = False
    pinned = False
    if cached and any(check.lean for check in checks):
        try:
            pinned = benchmark_state.clean_packages(ROOT)
        except (OSError, ValueError, KeyError, subprocess.CalledProcessError) as error:
            print(f'Cannot establish pinned Lean packages: {error}', flush=True)
    for check in checks:
        if args.list:
            print(f'{check.name}: {" ".join(check.command)}')
        else:
            print(f'Checking {check.name}', flush=True)
            cache = args.cache_dir if cached else None
            if cache is not None and not pinned and check.lean:
                print('  Running without reusing Lean evidence; package trees differ from their pins.', flush=True)
                cache = None
            state = run(check, Inputs(ROOT, cache), environment, cache)
            print(f'{check.name}: {state}', flush=True)


if __name__ == '__main__':
    main()
