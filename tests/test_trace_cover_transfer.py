from fractions import Fraction
from hashlib import sha256
import json
from math import gcd
import unittest

from experiments.farey_allocation import lattice_start, needed
from experiments.trace_cover_transfer import (
    HOLDOUT_CLASSES, ceiling_template, compile_partition, holdout_inputs)


class TransferTest(unittest.TestCase):
    def test_endpoint_bounds_without_an_interior_slope(self):
        cuts = [Fraction(1), Fraction(3, 2), Fraction(3, 2), Fraction(2)]
        slopes = [(2, 1), (3, 2), (1, 1)]
        template = compile_partition(slopes, cuts)
        for n in (35, 77, 143, 2537):
            windows, lengths = template.allocate(n)
            by_slope = dict(zip(template.slopes, zip(windows, lengths)))
            for (a, b), lo, hi in zip(slopes, cuts, cuts[1:]):
                (first, step), length = by_slope[a, b]
                self.assertEqual((first, step), lattice_start(n, a, b, 24))
                def cost(r):
                    return needed(n, a, b, r.numerator, r.denominator, first, step)
                self.assertEqual(length, max(cost(lo), cost(hi)))
                for j in range(9):
                    self.assertLessEqual(cost(lo+(hi-lo)*j/8), length)
            for p in range(2, n):
                if n%p:
                    continue
                q = n//p
                if not p <= q <= 2*p:
                    continue
                for (a, b), lo, hi in zip(slopes, cuts, cuts[1:]):
                    if lo <= Fraction(q, p) <= hi:
                        (first, step), length = by_slope[a, b]
                        diff = a*p+b*q-first
                        self.assertGreaterEqual(diff, 0)
                        self.assertEqual(diff%step, 0)
                        self.assertLess(diff//step, length)

    def test_public_residue_cap_for_all_small_products(self):
        for residue in (1, 5, 7, 11):
            template, info = ceiling_template(8, residue, 4, 3)
            source = int(info['source_input'])
            self.assertEqual(source%12, residue)
            _, base = template.allocate(source)
            for n in range(3, source+1):
                if n%12 != residue:
                    continue
                _, lengths = template.allocate(n)
                self.assertTrue(all(y <= x+1 for x, y in zip(base, lengths)))
                self.assertLessEqual(sum((z+2)//3 for z in lengths), info['universal_block_cap'])

    def test_rejects_uncovered_ranges_and_invalid_uses(self):
        for slopes, cuts in [([(1, 1)], [Fraction(3, 2), 2]),
                             ([(1, 1), (3, 2), (2, 1)], [1, 2, Fraction(3, 2), 2]),
                             ([(1, 1), (1, 1)], [1, Fraction(3, 2), 2]),
                             ([(2, 2)], [1, 2])]:
            with self.assertRaises(ValueError):
                compile_partition(slopes, cuts)
        template = compile_partition([(3, 2)], [1, 2])
        with self.assertRaises(ValueError):
            template.allocate(21)
        with self.assertRaises(ValueError):
            template.records(35, 1, 3, 32, 4, 2, 24, {})

    def test_prespecified_panel(self):
        inputs = holdout_inputs()
        digest = sha256(json.dumps([str(n) for n in inputs], separators=(',', ':')).encode()).hexdigest()
        self.assertEqual(digest, '81c5181d07366289a8f4f979bfe0e31966912821598e75de4ee75ba6a4423fa5')
        self.assertEqual([n%24 for n in inputs], list(HOLDOUT_CLASSES))
        self.assertEqual([n.bit_length() for n in inputs], [88, 89]*6)
        self.assertTrue(all(gcd(n, 6) == 1 for n in inputs))


if __name__ == '__main__':
    unittest.main()
