"""A wrong cubic square root must fail even when both reported factors are right."""

from copy import deepcopy
from pathlib import Path
from tempfile import TemporaryDirectory
import unittest

from experiments.cubic_trace_search import search
from scripts.cubic_trace_benchmark import THEOREM, trace_source
from scripts.factor import verify_file


class CubicTraceCertificateTests(unittest.TestCase):
    def test_kernel_rejects_altered_field_root(self):
        work = search(989, trace_cap=1)
        hit = work['arms'][-1]['first_hit']
        self.assertEqual(hit['divisors'], ['23', '43'])
        with TemporaryDirectory() as directory:
            proof = Path(directory) / 'CubicTrace.lean'
            proof.write_text(trace_source(989, work, hit))
            verify_file(proof, THEOREM)
            corrupted = deepcopy(hit)
            corrupted['field_roots'][0]['numerators'][0] += 1
            proof.write_text(trace_source(989, work, corrupted))
            with self.assertRaisesRegex(ValueError, 'decide'):
                verify_file(proof, THEOREM)
