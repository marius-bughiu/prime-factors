from collections import Counter
from math import gcd
import unittest

from experiments.affine_radix_holdout import draw_prime
from experiments.lifted_period_join import _lifted_table
from experiments.lifted_period_trace import (
    FRESH_N, SEED, TraceSeries, centered_table, compare, sweep,
)
from experiments.trace_folded_right import _layers


class LiftedPeriodTraceTests(unittest.TestCase):
    def test_trace_series_signed_ranges_and_nonunit_step_difference(self):
        n = 105
        for mode in ('direct', 'recurrence'):
            for h in (1, 2, 4, 11, 104):
                series = TraceSeries(n, h, pow(h, -1, n), Counter(), mode)
                for first in range(-7, 7):
                    for last in range(first - 1, 8):
                        actual = series.keys(13, pow(13, -1, n), first, last)
                        expected = []
                        for k in range(first, last + 1):
                            y = 13 * pow(h, k, n) % n
                            expected.append((y + pow(y, -1, n)) % n)
                        self.assertEqual(list(actual), expected)

    def test_centered_orbits_include_zero_and_midpoint_once(self):
        # Base 2 has order 8 here, so the comparison exercises repeated buckets.
        n, period, lower = 17, 12, 10
        power = pow(2, period, n)
        back = pow(power, -1, n)
        for moduli in ((), (3,), (4,), (3, 4)):
            groups = [(m, set(range(m))) for m in moduli]
            _, layers = _layers(groups, period, n, 2, power, back, lower, True, Counter())
            for lift in range(1, 7):
                limit = period * lift // 2
                positions = [t for t in range(limit + 1)
                             if all(t % m == 0 for m in (3, 4) if m not in moduli)]
                reference = _lifted_table(layers, n, period, lift, power, back, pow(power, lift, n),
                                          pow(back, lift, n), Counter())
                for mode in ('direct', 'recurrence'):
                    table = centered_table(layers, n, period, lift, power, back, Counter(), mode)
                    self.assertEqual(dict(table), dict(reference))
                    actual = sorted((t, trace) for trace, bucket in table.items() for t in bucket)
                    expected = [(t, (pow(2, t, n) + pow(2, -t, n)) % n) for t in positions]
                    self.assertEqual(actual, expected)

    def test_bucket_with_different_local_signs_recovers_proper_gcd(self):
        n, t, exponent = 77, 1, 11
        trace = (pow(2, t, n) + pow(2, -t, n)) % n
        y = pow(2, exponent, n)
        prepared = ([], 0, {trace: [t]}, y, pow(y, -1, n), 1, 1)
        for mode in ('stock', 'direct', 'recurrence'):
            result = sweep(n, 20, 1, dict(period=30, lifted_period=30), prepared, Counter(), mode)
            self.assertEqual(result, ('trace_mixed_gcd', gcd(pow(2, t, n) - y, n)))

    def test_fresh_draw_is_first_and_public_plan_matches(self):
        p, q = (draw_prime(side, 0, bits=46, seed=SEED) for side in (b'p', b'q'))
        self.assertNotEqual(p, q)
        self.assertEqual(p * q, FRESH_N)
        self.assertEqual(FRESH_N.bit_length(), 92)
        row = compare(FRESH_N, 46, rounds=1)
        self.assertEqual(row['factors'], list(map(str, sorted((p, q)))))
        self.assertEqual(row['methods']['recurrence']['lookups'], 11_774)
        self.assertEqual(row['methods']['recurrence']['signature_multiplications'], 41_514)
        self.assertLess(row['methods']['recurrence']['signature_multiplications'],
                        row['methods']['direct']['signature_multiplications'])
