import json
from math import gcd, isqrt
from pathlib import Path
from unittest import TestCase
from unittest.mock import patch

from experiments.near_smooth_control import KNOWN_INDICES, progression
from experiments.near_smooth_sum import ceil_sqrt, search, sum_bands


class NearSmoothSumTests(TestCase):
    def test_endpoints_cover_equal_width_divisors(self):
        for n in range(5, 800):
            if gcd(n, 6) != 1:
                continue
            for tolerance in (0, 3, 12):
                bands, _, _ = sum_bands(n, tolerance)
                bits = (n.bit_length() + 1) // 2
                for p in range(2, isqrt(n) + 1):
                    q, remainder = divmod(n, p)
                    if remainder or p.bit_length() != bits or q.bit_length() != bits:
                        continue
                    expected = set()
                    odd_part = 1
                    while 2*odd_part <= p+q+tolerance:
                        center = 2*odd_part
                        while center <= p+q+tolerance:
                            if abs(p+q-center) <= tolerance:
                                expected.add(center)
                            center *= 2
                        odd_part *= 3
                    covered = {b.center for b in bands if b.lower <= p <= b.upper
                               and b.first_sum <= p+q <= b.last_sum}
                    self.assertEqual(covered, expected, (n, tolerance, p))

    def test_trace_and_direct_mod24_scan(self):
        result = search(2537, 8)
        self.assertEqual((result['factor'], result['winning_center'], result['sum_error']), (43, 96, 6))
        self.assertEqual(result['work']['trace_windows'], 1)
        self.assertEqual(result['work']['square_tests'], 1)
        bands, _, _ = sum_bands(2537, 8)
        allowed = {r*(2537+1) % 24 for r in range(24) if gcd(r,24) == 1}
        self.assertEqual(result['direct_mod24_tests'], sum(s % 24 in allowed for s in
                         range(bands[0].first_sum, result['winning_sum']+1)))
        self.assertIsNone(search(2537, 0)['factor'])
        self.assertEqual(ceil_sqrt(25), 5)
        self.assertEqual(ceil_sqrt(26), 6)

    def test_window_budget_and_unsuccessful_height(self):
        result = search(2537, 8, max_windows=0)
        self.assertEqual(result['windows_checked'], 0)
        self.assertEqual(result['windows_remaining'], result['viable_windows'])
        self.assertIsNone(result['factor'])
        failed = {'excluded': False, 'short': False, 'divisors': [], 'rootless_modulus': None, 'work': {}}
        with patch('experiments.near_smooth_sum.polynomial_window', return_value=failed):
            receipts = []
            missed = search(132079, 8, exclusion_witnesses=receipts)
        self.assertIsNone(missed['factor'])
        self.assertTrue(missed['unresolved_windows'])
        self.assertEqual(missed['windows_remaining'], 0)
        self.assertFalse(receipts)
        # No integral sum fits the balanced interval at this product.
        self.assertFalse(search(15049, 32)['viable_windows'])

    def test_nonunits_and_exact_remaining_budget(self):
        # The small denominator factors 5 and 7 are not balanced factors in
        # these bands. A missed polynomial height must leave its band unresolved.
        for n in (625*677, 707*713):
            tolerance = 1 << (n.bit_length()//2)
            result = search(n, tolerance, max_windows=1)
            self.assertEqual(result['work']['ordinary_sextic_windows'], 1)
            self.assertIsNone(result['factor'])
            self.assertEqual(len(result['unresolved_windows']), 1)
            self.assertEqual(result['windows_remaining'], result['viable_windows']-1)
        unlimited = search(2537, 8)
        self.assertEqual(unlimited['factor'], search(2537, 8, max_windows=10**100)['factor'])
        for cap in (-1, 1.5):
            with self.assertRaises(ValueError):
                search(2537, 8, max_windows=cap)
        with self.assertRaises(ValueError):
            search(2537, -1)

    def test_independent_construction_seeds(self):
        path = Path(__file__).resolve().parents[1] / 'benchmarks/near-smooth-sum.json'
        cases = {row['id']: row for row in json.loads(path.read_text())}
        for version, error_bits in ((1, 160), (2, 399)):
            total, first, step = progression(version)
            p = first + KNOWN_INDICES[version]*step
            q = total-p
            row = cases[f'near-smooth-{error_bits}-2048']
            self.assertEqual(str(p*q), row['n'])
            self.assertEqual([str(p), str(q)], row['factors'])
            self.assertEqual(abs(total-int(row['winning_center'])).bit_length(), error_bits)
