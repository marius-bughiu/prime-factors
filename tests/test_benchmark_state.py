"""Incremental benchmark selection and receipt ownership on a tiny checkout."""

import contextlib
import io
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from scripts import benchmark_state as state


def case(name, complete=False):
    return dict(id=name, n='15', status='complete' if complete else 'partial',
                factors=['3', '5'] if complete else [], remaining=[] if complete else ['15'])


class RowCacheTests(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        self.root = Path(temp.name).resolve()
        self.cache = self.root / 'cache'
        for name in ('benchmarks', 'PrimeFactors', 'docs'):
            (self.root / name).mkdir()
        self.write('benchmarks/sibling.json', '1')
        self.write('PrimeFactors/Parent.lean', 'import PrimeFactors.Child\n')
        self.write('PrimeFactors/Child.lean', 'import Mathlib\n')
        self.write('PrimeFactors/Unrelated.lean', 'import Mathlib\n')
        self.cases = [('main.json', 'fermat', case('complete', True)),
                      ('more.json', 'reader', case('partial'))]
        self.executed = []
        self.serial = 0
        self.provenance = dict(commit='a'*40, repository='project', run_id='15', platform='one',
                               cpu='cpu-one', python='3.12', lean='4.19')

    def write(self, name, source):
        (self.root / name).write_text(source)

    def inputs(self, shared='shared-v1'):
        def digests(folder, glob):
            return {f.relative_to(self.root).as_posix(): state.digest(f.read_bytes())
                    for f in (self.root / folder).glob(glob)}
        return state.Inputs(self.root, shared, digests('benchmarks', '*.json'),
                            digests('PrimeFactors', '*.lean'), digests('docs', '*'))

    def measure(self, fixture, method, proofdir):
        self.executed.append(fixture['id'])
        row = dict(fixture, method=method, wall_seconds=0.1, verified=fixture['status']=='complete',
                   certificate=None)
        if method == 'fermat':
            for name in ('complete.lean', 'secondary.lean'):
                (proofdir / name).write_text('import PrimeFactors.Parent\n')
            row.update(certificate='proofs/complete.lean', extra={'exclusion': 'proofs/secondary.lean'})
        if method == 'reader':
            (self.root / 'benchmarks/sibling.json').read_text()
        if method == 'opaque':
            state._audit('subprocess.Popen', ('command', ['command'], str(self.root), None))
        return row

    def run_panel(self, shared='shared-v1'):
        with tempfile.TemporaryDirectory(dir=self.root) as tmp, contextlib.redirect_stdout(io.StringIO()):
            work = Path(tmp)
            proofs = work / 'proofs'
            proofs.mkdir()
            self.executed = []
            rows, hits, measured = state.run_cases(self.cases, self.measure, proofs, work,
                                                   self.provenance, self.inputs(shared), self.cache)
            state.publish_entries(work / 'entries', measured, self.cache)
            return rows, hits, {p.name: p.read_bytes() for p in proofs.iterdir()}

    def test_provenance_and_all_proofs_round_trip(self):
        first, hits, proofs = self.run_panel()
        self.assertEqual(hits, 0)
        self.assertEqual(set(proofs), {'complete.lean', 'secondary.lean'})
        self.provenance.update(commit='b'*40, run_id='16', cpu='cpu-two')
        second, hits, restored = self.run_panel()
        self.assertEqual((hits, self.executed, restored), (2, [], proofs))
        for old, new in zip(first, second):
            self.assertTrue(new['reused'])
            self.assertEqual(old['measurement'], new['measurement'])

    def test_sibling_and_transitive_proof_dependencies(self):
        self.run_panel()
        self.write('benchmarks/sibling.json', '2')
        self.assertEqual(self.run_panel()[1], 1)
        self.assertEqual(self.executed, ['partial'])
        self.write('PrimeFactors/Extra.lean', 'import Mathlib\n')
        self.write('PrimeFactors/Unrelated.lean', 'import Mathlib\n-- unrelated edit\n')
        self.assertEqual(self.run_panel()[1], 2)
        self.write('PrimeFactors/Child.lean', 'import Mathlib\n-- actual dependency\n')
        self.assertEqual(self.run_panel()[1], 1)
        self.assertEqual(self.executed, ['complete'])
        self.cases[0][2]['max_steps'] = 8
        self.assertEqual(self.run_panel()[1], 1)
        self.assertEqual(self.run_panel('shared-v2')[1], 0)
        self.assertEqual(set(p.name for p in self.cache.iterdir()), {'partial.json', 'complete.json'})

    def test_opaque_and_observed_unusual_inputs(self):
        self.cases.append(('extra.json', 'opaque', case('child-process')))
        self.run_panel()
        self.write('PrimeFactors/Third.lean', 'import Mathlib')
        self.assertEqual(self.run_panel()[1], 2)
        self.assertEqual(self.executed, ['child-process'])
        source = 'docs/spec.md'
        self.write(source, 'one')
        with state.observe(self.root, local := state.Observed()):
            (self.root / source).read_text()
            (self.root / 'PrimeFactors/Child.lean').read_text()
        deps = state.dependencies(self.inputs(), 'reader', {}, state.Observed(), local)
        self.write(source, 'two')
        self.assertFalse(state.compatible(self.inputs(), deps))
        self.assertIn('PrimeFactors/Child.lean', deps['lean'])
        self.assertIsNone(state.project_imports('import Unknown.Dependency'))
        self.assertIsNone(state.project_imports('import Mathlib\n#eval IO.println 1'))

    def classifier_inputs(self):
        # The Git path inventory is the only external operation in input_hashes.
        files = [f for directory in ('scripts', 'experiments', 'benchmarks', 'PrimeFactors', 'docs')
                 for f in (self.root / directory).rglob('*') if f.is_file()]
        inventory = b''.join(os.fsencode(f.relative_to(self.root)) + b'\0' for f in files)
        with patch.object(state.subprocess, 'check_output', return_value=inventory):
            return state.input_hashes(self.root, {'python': 'test'})

    def prepare_classifier(self):
        for name in ('scripts', 'experiments'):
            (self.root / name).mkdir()
        self.write('scripts/benchmark.py', 'from experiments import active\n')
        self.write('scripts/factor.py', '')
        self.write('experiments/active.py', 'from . import child as child_alias\n')
        self.write('experiments/child.py', 'value = 1\n')

    def test_separate_experiments_preserve_precise_rows_but_opaque_sees_all(self):
        self.prepare_classifier()
        self.inputs = lambda _shared: self.classifier_inputs()
        self.cases.append(('extra.json', 'opaque', case('child-process')))
        self.run_panel()
        self.write('experiments/new_study.py', 'value = 1\n')
        self.write('benchmarks/unrelated-study.json', '[]')
        self.assertEqual(self.run_panel()[1], 2)
        self.assertEqual(self.executed, ['child-process'])
        self.write('experiments/child.py', 'from . import new_study\n')
        self.assertEqual(self.run_panel()[1], 0)
        self.write('experiments/new_study.py', 'value = 2\n')
        self.assertEqual(self.run_panel()[1], 0)
        # An unknown process cannot provide observable inputs to the parent.
        self.assertEqual(self.run_panel()[1], 2)

    def test_failed_reads_and_directory_observations(self):
        self.prepare_classifier()
        absent = ('benchmarks/optional.json', 'experiments/optional.py')
        for name in absent:
            with self.subTest(name=name):
                with state.observe(self.root, local := state.Observed()):
                    with self.assertRaises(FileNotFoundError):
                        (self.root/name).read_bytes()
                deps = state.dependencies(self.classifier_inputs(), 'reader', {}, state.Observed(), local)
                self.assertTrue(state.compatible(self.classifier_inputs(), deps))
                self.write(name, '1')
                self.assertFalse(state.compatible(self.classifier_inputs(), deps))
        with state.observe(self.root, local := state.Observed()):
            list((self.root/'experiments').iterdir())
        deps = state.dependencies(self.classifier_inputs(), 'reader', {}, state.Observed(), local)
        self.write('experiments/another.py', '')
        self.assertFalse(state.compatible(self.classifier_inputs(), deps))

    def test_unobserved_metadata_and_dynamic_imports_force_fresh_results(self):
        self.prepare_classifier()
        self.inputs = lambda _shared: self.classifier_inputs()
        for source in ("from os import stat as probe\n", "from importlib import import_module as load\n",
                       "def check(path): return path.is_file()\n", "import os\nprobe = os.access\n",
                       "def check(path): return path.resolve(strict=True)\n"):
            with self.subTest(source=source):
                self.write('experiments/child.py', source)
                self.assertIsNotNone(self.classifier_inputs().guard)
                self.run_panel()
                self.assertEqual(self.run_panel()[1], 0)

    def test_import_candidates_include_new_shadow_modules_and_package_initializers(self):
        self.prepare_classifier()
        self.write('experiments/active.py', 'import math\nfrom .optional import value\n')
        baseline = self.classifier_inputs()
        self.write('experiments/optional.py', 'value = 1')
        optional = self.classifier_inputs()
        self.assertNotEqual(optional.shared, baseline.shared)
        self.write('experiments/math.py', 'value = 2')
        shadow = self.classifier_inputs()
        self.assertIn('experiments/math.py', shadow.python)
        self.assertNotEqual(shadow.shared, optional.shared)
        (self.root/'experiments/optional').mkdir()
        self.write('experiments/optional/__init__.py', 'from .. import child\n')
        self.assertNotEqual(self.classifier_inputs().shared, shadow.shared)

    def test_ignored_missing_and_existing_input(self):
        self.prepare_classifier()
        (self.root/'build').mkdir()
        path = self.root/'build/table.json'
        with state.observe(self.root, missing := state.Observed()):
            with self.assertRaises(FileNotFoundError):
                path.read_text()
        inputs = self.classifier_inputs()
        deps = state.dependencies(inputs, 'reader', {}, state.Observed(), missing)
        self.assertTrue(state.compatible(inputs, deps))
        path.write_text('input')
        self.assertFalse(state.compatible(inputs, deps))
        with state.observe(self.root, local := state.Observed()):
            path.read_text()
        self.assertIsNone(state.dependencies(inputs, 'reader', {}, state.Observed(), local))

    def test_unknown_child_io_and_bare_sibling_imports(self):
        self.prepare_classifier()
        self.write('scripts/factor.py', "from helper import calculate\n")
        self.write('scripts/helper.py', "import experiments.extra\n")
        self.write('experiments/extra.py', 'value = 1')
        inputs = self.classifier_inputs()
        self.assertIn('experiments/extra.py', inputs.python)
        self.assertFalse(inputs.child_known)
        with state.observe(self.root, local := state.Observed()):
            state._audit('subprocess.Popen', (state.sys.executable, [state.sys.executable,
                         'scripts/factor.py', '15', '--verify'], str(self.root), None))
        self.assertIsNone(state.dependencies(inputs, 'reader', {}, state.Observed(), local))
        self.write('experiments/extra.py', 'value = 2')
        self.assertNotEqual(self.classifier_inputs().shared, inputs.shared)
        self.write('experiments/child.py', "if __name__ == '__main__':\n    table.exists()\n")
        self.assertIsNone(self.classifier_inputs().guard)

    def test_unsafe_earlier_loader_prevents_reusing_a_later_row(self):
        self.cases = [('more.json', 'reader', case('first')), ('more.json', 'reader', case('second'))]
        self.run_panel()
        self.assertEqual(self.run_panel()[1], 2)
        original_measure = self.measure
        def changed_measure(fixture, method, directory):
            if fixture['id'] == 'first':
                list((self.root/'benchmarks').glob('*.json'))
            return original_measure(fixture, method, directory)
        self.measure = changed_measure
        self.cases[0][2]['changed'] = True
        self.assertEqual(self.run_panel()[1], 0)
        self.assertEqual(self.executed, ['first', 'second'])

    def test_unreviewed_lean_file_access_stays_uncached_even_on_a_broad_row(self):
        inputs = self.inputs()
        local = state.Observed()
        local.opaque = True
        source = {'probe.lean': 'import Mathlib\n#eval IO.FS.readFile "build/auxiliary.txt"'}
        self.assertIsNone(state.dependencies(inputs, 'probe', source, state.Observed(), local))

    def test_corruption_and_incomplete_proof_fall_back_without_using_cache_code(self):
        self.run_panel()
        record = self.cache/'complete.json'
        saved = json.loads(record.read_bytes())
        saved['payload']['proofs'].pop('secondary.lean')
        saved['payload']['proof_hashes'].pop('secondary.lean')
        saved['sha256'] = state.digest(state.encoded(saved['payload']))
        record.write_text(json.dumps(saved))
        self.assertEqual(self.run_panel()[1], 1)
        self.assertEqual(self.executed, ['complete'])
        (self.cache/'partial.json').write_bytes(b'corrupt')
        self.assertEqual(self.run_panel()[1], 1)
        self.assertEqual(self.executed, ['partial'])

    def test_publish_replaces_retired_rows_and_preserves_named_standalone(self):
        from scripts.verify_checks import CHECKS
        names = {name for check in CHECKS for name in check.outputs}
        self.assertIn('rectangular-exact-fresh-2048.lean', names)
        site = self.root/'site'
        staged = self.root/'stage'
        for target in (site, staged):
            (target/'proofs').mkdir(parents=True)
            (target/'results.json').write_text(target.name)
        (site/'index.html').write_text('unrelated')
        for name in names | {'retired.lean'}:
            (site/'proofs'/name).write_text('previous')
        (staged/'proofs'/'current.lean').write_text('current')
        state.publish_site(staged, site, names)
        self.assertEqual({p.name for p in (site/'proofs').iterdir()}, names | {'current.lean'})
        self.assertEqual((site/'index.html').read_text(), 'unrelated')
        self.assertEqual((site/'results.json').read_text(), 'stage')
