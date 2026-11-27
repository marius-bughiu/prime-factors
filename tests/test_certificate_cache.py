import json
import os
from pathlib import Path
from tempfile import TemporaryDirectory
import unittest
from unittest.mock import Mock, patch

from scripts import certificate_cache as cache


class CertificateCacheTests(unittest.TestCase):
    def test_success_requires_identical_proof_and_verification_context(self):
        with TemporaryDirectory() as tmp, patch.dict(os.environ, {
                cache.CACHE: tmp, cache.CONTEXT: 'a' * 64}):
            proof = Path(tmp) / 'input.lean'
            verify = Mock()
            proof.write_text('first')
            original = cache.check_generated(proof, verify)
            self.assertFalse(original['reused'])
            self.assertEqual(dict(original, reused=True), cache.check_generated(proof, verify))
            proof.write_text('second')
            self.assertFalse(cache.check_generated(proof, verify)['reused'])
            os.environ[cache.CONTEXT] = 'b' * 64
            self.assertFalse(cache.check_generated(proof, verify)['reused'])
            self.assertEqual(verify.call_count, 3)
            record = Path(tmp, original['key'] + '.json')
            record.write_text(json.dumps(dict(original, key='wrong')))
            os.environ[cache.CONTEXT] = 'a' * 64
            proof.write_text('first')
            self.assertFalse(cache.check_generated(proof, verify)['reused'])
            self.assertEqual(verify.call_count, 4)

    def test_failed_checks_never_seed_cache_and_full_checks_ignore_it(self):
        with TemporaryDirectory() as tmp, patch.dict(os.environ, {
                cache.CACHE: tmp, cache.CONTEXT: 'c' * 64}):
            proof = Path(tmp) / 'example.lean'
            proof.write_text('error')
            with self.assertRaises(ValueError):
                cache.check_generated(proof, Mock(side_effect=ValueError('rejected')))
            self.assertFalse(list(Path(tmp).glob('*.json')))
            verify = Mock()
            cache.check_generated(proof, verify)
            cache.configure(None)
            self.assertIsNone(cache.check_generated(proof, verify))
            self.assertEqual(verify.call_count, 2)

    def test_context_tracks_transitive_imports_and_pinned_toolchain(self):
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            library = root / '.lake/build/lib/lean'
            for name in ('scripts/factor.py', 'scripts/certificate_cache.py', 'scripts/Audit.lean',
                         'lean-toolchain', 'lake-manifest.json', 'lakefile.toml'):
                path = root / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(name)
            for name in ('Entry', 'Ancestor', 'Unrelated'):
                path = root / 'PrimeFactors' / (name + '.lean')
                path.parent.mkdir(exist_ok=True)
                path.write_text(name)
                binary = library / 'PrimeFactors' / (name + '.olean')
                binary.parent.mkdir(parents=True, exist_ok=True)
                binary.write_text(name)

            def lean(*args):
                if args == ('--version',):
                    return 'pinned compiler'
                if args == ('--print-prefix',):
                    return str(root / 'toolchain')
                if args == ('--deps', 'PrimeFactors/Entry.lean'):
                    return str(library / 'PrimeFactors/Ancestor.olean')
                self.assertEqual(args, ('--deps', 'PrimeFactors/Ancestor.lean'))
                return ''

            with patch.object(cache, 'ROOT', root), patch.object(cache, 'MODULES', ('Entry',)), \
                    patch.object(cache, 'lean_output', side_effect=lean):
                initial = cache.context_digest()
                (root / 'PrimeFactors/Unrelated.lean').write_text('changed')
                self.assertEqual(initial, cache.context_digest())
                (root / 'PrimeFactors/Ancestor.lean').write_text('changed')
                after_source = cache.context_digest()
                self.assertNotEqual(initial, after_source)
                (root / 'lean-toolchain').write_text('new version')
                self.assertNotEqual(after_source, cache.context_digest())
