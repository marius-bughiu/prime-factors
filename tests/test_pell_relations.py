import unittest
from itertools import combinations
from math import gcd, isqrt, prod

from experiments.pell_relations import _dependencies, _private_parts, search


class PellRelationsTest(unittest.TestCase):
    def test_coprime_refinement_finds_the_entire_signed_square_kernel(self):
        for values in ([1, -1, -1, 4], [45, -75, 3, -5, 25, 81],
                       [2, 8, 18, 50, 128], [121, 165, 75, 99, 11, 15]):
            obtained = {0}
            for basis in _dependencies(values):
                obtained |= {mask ^ basis for mask in obtained}
            expected = set()
            for count in range(len(values) + 1):
                for subset in combinations(range(len(values)), count):
                    product = prod(values[i] for i in subset)
                    if product >= 0 and isqrt(product)**2 == product:
                        expected.add(sum(1 << i for i in subset))
            self.assertEqual(obtained, expected)

    def test_private_parts_include_all_powers_and_preserve_singleton_squares(self):
        for values in ([], [1], [23**2], [1, 12, 18, 100, 12], [2**19*7, 2*3**11, 5**6]):
            private = _private_parts(values)
            for i, (v, part) in enumerate(zip(values, private)):
                self.assertEqual(v % part, 0)
                self.assertEqual(gcd(part, v//part), 1)
                others = prod(values[:i] + values[i+1:])
                self.assertEqual(gcd(part, others), 1)
                shared = v // part
                while shared != 1:
                    common = gcd(shared, others)
                    self.assertGreater(common, 1)
                    shared //= common

    def test_external_primes_are_removed_before_the_square_test(self):
        self.assertEqual(_private_parts([45, 14], 15), [1, 14])
        self.assertEqual(_private_parts([3**25*7], 3), [7])
        # A supplied support only strengthens exclusions. Splitting uses
        # exactly the original norms, even if every private part is removed.
        self.assertEqual(search(21490481, 1, 30, external=2*3*5*7*11*13)['factor'], 4421)

    def test_first_split_in_prefix(self):
        short = search(21490481, 1, 29)
        self.assertEqual((short['factor'], short['dependencies'], short['tested']), (None, 6, 6))
        longer = search(21490481, 1, 30)
        self.assertEqual((longer['factor'], longer['selected_steps']), (4421, [6, 8, 14, 30]))
        self.assertFalse(longer['center'])

    def test_empty_prefix_and_denominator_gcd(self):
        self.assertEqual(search(77, 1, 0)['rows'], 0)
        work = search(77, 1, 20)
        self.assertIn(work['factor'], (7, 11))
        self.assertEqual(work['outcome'], 'denominator')
        with self.assertRaises(ValueError):
            search(77, 77, 100)
