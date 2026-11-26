import json
from itertools import combinations
from math import gcd, isqrt, prod
from pathlib import Path
import unittest

from experiments.weighted_square_triples import ARMS, compare, summarize


class WeightedSquareTriplesTests(unittest.TestCase):
    @staticmethod
    def rows(n):
        # Generate the admissible progression directly from its two inequalities.
        initial, extra = [], []
        for weight in range(1, 9):
            stride = gcd(2*(n+weight), 24)
            label = isqrt(4*n*weight)
            while label**2 < 4*n*weight or (label-n-weight) % stride:
                label += 1
            for rank in range(72):
                row = label, label**2-4*n*weight
                (initial if rank < 2 else extra).append(row)
                label += stride
        return initial, extra

    def test_pilot_and_matched_fallback(self):
        result = compare(2100271, all_subsets=True)
        self.assertIsNone(result['initial'])
        self.assertIsNone(result['pair'])
        self.assertEqual(result['genuine_triple'], result['triple'])
        self.assertEqual(result['triple']['rows'], [[3, 1], [4, 0], [7, 0]])
        self.assertEqual(result['triple']['excesses'], ['57424', '873', '21312'])
        self.assertEqual(result['triple']['square_root'], '1033632')
        self.assertEqual(result['triple']['divisor'], '1637')
        self.assertEqual(result['extra_single']['rows'], [[1, 2]])
        self.assertEqual(result['extra_single']['divisor'], '1283')
        self.assertEqual(result['subsets']['square_subsets'], 1)
        self.assertEqual(result['work']['extra_single_splitting_tests'], 4)

    def test_full_costs_and_square_branches(self):
        for n in (49, 77, 221, 2100271):
            with self.subTest(n=n):
                initial, extra = self.rows(n)
                result = compare(n)
                work = result['work']
                inputs = (combinations(initial, 1), combinations(initial, 2),
                          combinations(initial, 3), combinations(extra, 1))
                for arm, subsets in zip(ARMS, inputs):
                    count = squares = minus = plus = splits = genuine = 0
                    square_bits = gcd_bits = 0
                    for subset in subsets:
                        count += 1
                        operand = prod(v for _, v in subset)
                        square_bits = max(square_bits, operand.bit_length())
                        root = isqrt(operand)
                        if root**2 != operand:
                            continue
                        squares += 1
                        left = prod(a for a, _ in subset)
                        gcd_bits = max(gcd_bits, n.bit_length(), (left+root).bit_length(),
                                       abs(left-root).bit_length())
                        minus_hit = 1 < gcd(n, left-root) < n
                        plus_hit = 1 < gcd(n, left+root) < n
                        minus += minus_hit
                        plus += plus_hit
                        if minus_hit or plus_hit:
                            splits += 1
                            genuine += all(isqrt(v)**2 != v for _, v in subset)
                    self.assertEqual([work[f'{arm}_{k}'] for k in (
                        'tests', 'squares', 'minus_gcds', 'plus_gcds', 'proper_minus',
                        'proper_plus', 'splitting_tests')],
                        [count, squares, squares, squares, minus, plus, splits])
                    self.assertEqual(result['max_operand_bits'][arm], square_bits)
                    self.assertEqual(result['max_operand_bits'][arm+'_gcd'], gcd_bits)
                    self.assertEqual(result[arm] is not None, bool(splits))
                    if arm == 'triple':
                        self.assertEqual(work['genuine_triple_splits'], genuine)

    def test_subset_count_including_zero_and_multiple_dependencies(self):
        for n in (49, 77):
            initial, _ = self.rows(n)
            products = [1]
            for _, excess in initial:
                products.extend([prior*excess for prior in products])
            result = compare(n, all_subsets=True)['subsets']
            self.assertEqual(result['zero_rows'], sum(v == 0 for _, v in initial))
            self.assertEqual(result['nonempty_subsets'], len(products)-1)
            self.assertEqual(result['square_subsets'], sum(isqrt(v)**2 == v for v in products[1:]))

    def test_full_size_subsets_and_costs(self):
        path = Path(__file__).resolve().parents[1]/'benchmarks/factor-sum-quantile.json'
        cases = [row for row in json.loads(path.read_text()) if int(row['n']).bit_length() == 2048]
        self.assertEqual(len(cases), 2)
        for case in cases:
            result = compare(int(case['n']), all_subsets=True)
            self.assertEqual((result['subsets']['private_pruned'], result['subsets']['pruning_rounds'],
                              result['subsets']['square_subsets']), (16, 1, 0))
            for arm, tests in zip(ARMS, (16, 120, 560, 560)):
                self.assertEqual(result['work'][arm+'_tests'], tests)
                self.assertEqual(result['work'][arm+'_squares'], 0)
                self.assertIsNone(result[arm])

    def test_summary_overlaps_and_inputs(self):
        result = summarize([2100271])
        self.assertEqual(result['overlap'], {'triple + extra_single': 1})
        self.assertEqual(result['counts']['genuine_and_extra_added'], 1)
        self.assertEqual(result['counts']['genuine_only'], 0)
        self.assertEqual(result['counts']['extra_only'], 0)
        for n in (0, 1, 2, 3, 6):
            with self.assertRaises(ValueError):
                compare(n)
