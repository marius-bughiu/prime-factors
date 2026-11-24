import json
from pathlib import Path
import unittest
from unittest.mock import patch

from experiments import crt_holdout


class CrtHoldoutTest(unittest.TestCase):
    def test_sample_and_report_replay(self):
        path = Path(__file__).resolve().parents[1] / 'research' / 'crt-holdout.json'
        report = json.loads(path.read_text())
        sample = list(crt_holdout.draw_sample())
        self.assertEqual(len(sample), 64)
        self.assertEqual((sample[0][0], sample[0][1]), (2, 533768368657277250656153))
        self.assertEqual(len({n for _, n, _ in sample}), 64)
        self.assertEqual(len(report['cases']), len(sample))
        for row, (attempt, n, primes) in zip(report['cases'], sample):
            self.assertEqual((row['attempt'], row['n'], row['expected_factors']),
                             (attempt, str(n), [str(p) for p in primes]))
            self.assertEqual(n.bit_length(), 79)
            self.assertEqual([p.bit_length() for p in primes], [40, 40])
            self.assertLess(primes[0], primes[1])
            for result in row['methods'].values():
                if result['factors']:
                    self.assertEqual(result['factors'], row['expected_factors'])
                    self.assertEqual(result['remaining'], [])
                else:
                    self.assertEqual(result['remaining'], [row['n']])
        self.assertEqual(crt_holdout.summarize(report['cases']), report['patterns'])

    def test_methods_receive_only_product_and_fixed_budgets(self):
        n = 123456789
        with (patch.object(crt_holdout, 'crt_search') as roots,
              patch.object(crt_holdout, 'cf_search') as fractions):
            crt_holdout.run_methods(n)
        self.assertEqual([call.args for call in roots.call_args_list], [(n,), (n,)])
        self.assertEqual([call.kwargs for call in roots.call_args_list], [
            dict(prime_count=12, threshold_bits=-4, hit_cap=1001, subset_size=3),
            dict(prime_count=12, threshold_bits=-2, hit_cap=10000, subset_size=3),
        ])
        fractions.assert_called_once_with(n, multiplier=1, max_steps=5138)
