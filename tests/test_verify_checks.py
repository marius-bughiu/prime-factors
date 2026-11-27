import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import Mock, patch

from scripts import verify_checks
from scripts.verify_checks import CHECKS, Check, Inputs, experiment, run


class VerifyChecksTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name) / 'repo'
        self.cache = Path(self.temp.name) / 'state'
        self.put('scripts/verify_checks.py', '# planner')
        self.put('experiments/driver.py', 'from experiments import adapter\n')
        self.put('experiments/adapter.py', 'from .shared import constant\n')
        self.put('experiments/shared.py', 'constant = 7\n')
        self.put('experiments/unrelated.py', 'print("ignored")')
        self.put('research/input.json', '1')
        self.put('research/other.json', '1')
        self.put('PrimeFactors/Theorem.lean', 'example : True := trivial')
        self.check = experiment('driver', '--check', data=('research/input.json',))

    def put(self, path, s):
        name = self.root/path
        name.parent.mkdir(parents=True, exist_ok=True)
        name.write_text(s)
        return name

    def key(self, check=None, environment='test-runtime'):
        return Inputs(self.root).fingerprint(check or self.check, environment)

    def test_local_dependency_transitivity_and_unrelated_files(self):
        original = self.key()
        self.put('experiments/unrelated.py', '# updated')
        self.put('research/other.json', '2')
        self.put('PrimeFactors/Theorem.lean', 'theorem t : True := trivial')
        self.assertEqual(self.key(), original)
        self.put('experiments/shared.py', 'constant = 42\n')
        self.assertNotEqual(self.key(), original)
        key = self.key()
        self.put('research/input.json', '2')
        self.assertNotEqual(self.key(), key)
        key = self.key()
        (self.root/'research/input.json').unlink()
        self.assertNotEqual(self.key(), key)
        self.assertNotEqual(self.key(), self.key(environment='different-interpreter'))

    def test_fallback_groups_command_and_toolchain(self):
        check = experiment('driver', data=('research',), lean=True)
        previous = self.key(check)
        self.put('research/new.json', '{}')
        self.assertNotEqual(self.key(check), previous)
        previous = self.key(check)
        self.put('PrimeFactors/New.lean', '#check Nat')
        self.assertNotEqual(self.key(check), previous)
        previous = self.key(check)
        self.put('lean-toolchain', 'new pinned compiler')
        self.assertNotEqual(self.key(check), previous)
        self.assertNotEqual(self.key(check),
                            self.key(experiment('driver', '--check', data=('research',), lean=True)))
        self.put('experiments/driver.py', 'import importlib\nimportlib.import_module("plugin")\n')
        previous = self.key()
        self.put('experiments/plugin.py', 'print("new")')
        self.assertNotEqual(self.key(), previous)

    def test_unit_tests_invalidate_for_changed_tests_and_new_test(self):
        check = CHECKS[0]
        self.assertEqual(check.name, 'unit-tests')
        self.assertEqual(check.command, ('python3', '-m', 'unittest', 'discover', '-s', 'tests'))
        key = self.key(check)
        self.put('tests/test_something.py', 'import unittest')
        self.assertNotEqual(self.key(check), key)
        key = self.key(check)
        self.put('tests/test_something.py', 'import unittest\n')
        self.assertNotEqual(self.key(check), key)
        for filename in ('site/index.html', 'site/findings.json', 'scripts/render_site.py',
                         '.github/workflows/verify.yml'):
            with self.subTest(filename=filename):
                key = self.key(check)
                self.put(filename, 'changed template, fixture or workflow')
                self.assertNotEqual(self.key(check), key)

    def test_success_only_restore_repair_and_no_cache(self):
        check = Check('fixture', ('tool', 'check'), ('research/input.json',), outputs=('a.lean',))
        record = self.cache/'checks/fixture.json'
        output = self.root/'build/site/proofs/a.lean'
        proof = 'example : True := trivial\n'
        def command(argv, *, cwd, check):
            self.assertTrue(check)
            self.assertEqual(cwd, self.root)
            self.put('build/site/proofs/a.lean', proof)
        execute = Mock(side_effect=command)
        def check_once(cache):
            return run(check, Inputs(self.root), 'runtime', cache, execute)
        self.assertEqual(check_once(self.cache), 'ran')
        output.unlink()
        self.assertEqual(check_once(self.cache), 'reused')
        self.assertEqual(output.read_text(), proof)
        self.assertEqual(execute.call_count, 1)
        damaged = json.loads(record.read_text())
        damaged['outputs']['a.lean']['source'] += '-- changed proof'
        record.write_text(json.dumps(damaged))
        self.assertEqual(check_once(self.cache), 'ran')
        record.write_text('{truncated')
        self.assertEqual(check_once(self.cache), 'ran')
        self.assertEqual(check_once(None), 'ran')
        self.assertEqual(check_once(None), 'ran')
        self.put('research/input.json', 'now different')
        previous = record.read_bytes()
        with self.assertRaises(subprocess.CalledProcessError):
            run(check, Inputs(self.root), 'runtime', self.cache,
                Mock(side_effect=subprocess.CalledProcessError(1, 'tool')))
        self.assertEqual(record.read_bytes(), previous)
        self.assertFalse(output.exists())
        with self.assertRaises(FileNotFoundError):
            run(check, Inputs(self.root), 'runtime', self.cache, Mock())
        self.assertEqual(record.read_bytes(), previous)
        self.assertEqual(check_once(self.cache), 'ran')

    def test_unknown_subprocess_runs_each_time(self):
        self.put('experiments/shared.py', 'import subprocess as child\nconstant=child.run\n')
        execute = Mock()
        for _ in range(2):
            self.assertEqual(run(self.check, Inputs(self.root), 'runtime', self.cache, execute), 'ran')
        self.assertEqual(execute.call_count, 2)
        self.assertFalse((self.cache/'checks/driver.json').exists())

    def test_only_exact_git_provenance_commands_are_classified(self):
        self.put('experiments/driver.py', 'from scripts import certificate_cache\n')
        for command in ("['git', 'status', '--porcelain']", "['git', 'rev-parse', 'HEAD']"):
            source = f'import subprocess\nsubprocess.check_output({command}, cwd=ROOT)\n'
            self.put('scripts/certificate_cache.py', source)
            self.key()
            for changed in (source.replace('], cwd', ", 'extra'], cwd"),
                            source.replace('cwd=ROOT', 'cwd=ROOT, shell=True')):
                self.put('scripts/certificate_cache.py', changed)
                with self.assertRaises(verify_checks.UntrackedProcess):
                    self.key()

    def test_registered_python_receipts_have_resolved_local_imports(self):
        for check in CHECKS:
            if check.name == 'unit-tests' or check.command[:2] != ('python3', '-m'):
                continue
            with self.subTest(check=check.name):
                entry = verify_checks.ROOT / (check.command[2].replace('.', '/') + '.py')
                sources = verify_checks.local_imports(verify_checks.ROOT, entry)
                self.assertIsNotNone(sources)
                self.assertIn(entry, sources)

    def test_concurrent_input_change_creates_no_success_record(self):
        def change(*args, **kwargs):
            self.put('research/input.json', 'edited during verification')
        with self.assertRaisesRegex(RuntimeError, 'changed during'):
            run(self.check, Inputs(self.root), 'runtime', self.cache, change)
        self.assertFalse((self.cache/'checks/driver.json').exists())

    def test_dirty_package_tree_bypasses_all_lean_records(self):
        args = ['verify_checks.py', '--cache-dir', str(self.cache), '--only', 'unit-tests',
                '--only', 'many_character_receipt', '--only', 'high_word_sum_ranking']
        with patch('sys.argv', args), patch.object(verify_checks, 'ROOT', self.root), \
                patch.object(verify_checks.benchmark_state, 'runtime_key', return_value={}), \
                patch.object(verify_checks.benchmark_state, 'clean_packages', return_value=False) as pinned, \
                patch.object(verify_checks, 'run', return_value='ran') as runner:
            verify_checks.main()
        pinned.assert_called_once_with(self.root)
        self.assertEqual([c.args[-1] for c in runner.call_args_list], [None, None, self.cache])

    def test_independent_checks_have_unique_ids_and_output_names(self):
        self.assertEqual(len({check.name for check in CHECKS}), len(CHECKS))
        outputs = [name for check in CHECKS for name in check.outputs]
        self.assertEqual(len(outputs), len(set(outputs)))
        self.assertIn('intermediate-menu-exclusion-fresh-2048.lean', outputs)
        self.assertIn('rectangular-exact-crossed-2048.lean', outputs)
