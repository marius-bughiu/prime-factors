"""Incremental benchmark selection and receipt ownership on a tiny checkout."""

import contextlib
import io
import json
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
