from copy import deepcopy
from fractions import Fraction
from pathlib import Path
from tempfile import TemporaryDirectory
import unittest
from unittest.mock import patch

from experiments.trace_cover import solve
from scripts import benchmark_state
from scripts.factor import render_certificate, verify_file
from scripts.trace_cover_certificate import THEOREM, check_schedule


class TraceCoverCertificateTest(unittest.TestCase):
    def test_successful_cleanup_preserves_benchmark_dependency_tracking(self):
        result = solve(43*59, 3, 2)
        with TemporaryDirectory() as directory:
            output = Path(directory).resolve()
            observed = benchmark_state.Observed(output)
            with patch('scripts.trace_cover_certificate.verify_file') as verify:
                with benchmark_state.observe(output.parent, observed):
                    check_schedule(43*59, 3, 2, result, Fraction(2), output/'Combined.lean')
            verify.assert_called_once()
            self.assertFalse(observed.unsafe)
            self.assertEqual([path.name for path in output.iterdir()], ['Combined.lean'])

    def test_factor_proof_and_schedule_share_a_file(self):
        n = 43 * 59
        result = solve(n, 3, 2)
        with TemporaryDirectory() as directory:
            proof = Path(directory) / 'Combined.lean'
            factors = render_certificate(n, [43, 59])
            proof.write_text(factors)
            self.assertEqual(check_schedule(n, 3, 2, result, Fraction(2), proof), THEOREM)
            self.assertIn(factors.rstrip(), proof.read_text())
            verify_file(proof)

    def test_sparse_ticket_tree_handles_repeated_prices(self):
        n = 1234891
        result = solve(n, 2, 1)
        self.assertGreater(max(w for _, w in result['prices']), 1)
        with TemporaryDirectory() as directory:
            path = Path(directory) / 'Tickets.lean'
            self.assertEqual(check_schedule(n, 2, 1, result, Fraction(2), path, sparse=True), THEOREM)
            self.assertIn('SparseTraceDual.lower_of_batch', path.read_text())

    def test_geometry_cannot_substitute_an_incomplete_catalogue(self):
        n = 2537
        # On the singleton interval at 1 the omitted direction is unused.
        right = Fraction(1)
        result = solve(n, 2, 2, right=right)
        forged = deepcopy(result)
        del forged['windows'][-1]
        del forged['budgets'][-1]
        with TemporaryDirectory() as directory:
            proof = Path(directory) / 'Existing.lean'
            proof.write_text(render_certificate(n, [43, 59]))
            original = proof.read_bytes()
            with self.assertRaisesRegex(ValueError, 'decide|false|True'):
                check_schedule(n, 2, 2, forged, right, proof)
            self.assertEqual(proof.read_bytes(), original)
