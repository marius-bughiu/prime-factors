from collections import Counter
from itertools import combinations, product
from math import gcd
import unittest

from experiments.cubic_trace_search import (
    BOUND, POINTS, characteristic, character_places, character_word, check_subset,
    collect, evaluate, kernels, multiply_by_alpha, primitive_rows, search, select_polynomial,
)


class CubicTraceSearchTests(unittest.TestCase):
    def test_public_polynomials_and_finite_irreducibility(self):
        for n in (989, 1915966849, 538242898783, 2**2047+19):
            work = Counter()
            m, f, cert = select_polynomial(n, work)
            self.assertEqual(evaluate(f, m), n)
            self.assertTrue(all(evaluate(f, r) % cert for r in range(cert)))
            self.assertTrue(all(-m//2 <= c <= m//2 for c in f[:2]))
        self.assertEqual((len(POINTS), len(primitive_rows(80, 16)), len(primitive_rows(160, 32))),
                         (415, 1583, 6361))
        self.assertTrue(all(gcd(a, b) == 1 and b > 0 for a, b in POINTS))

    def test_characteristic_matches_three_independent_integer_embeddings(self):
        # On a split test ring, directly form the three conjugate values.
        for roots in ((-3, 1, 5), (2, 2, -4)):
            a, b, c = roots
            f = (-a*b*c, a*b+b*c+a*c, -sum(roots))
            for v in product(range(-1, 2), repeat=3):
                values = [sum(t*r**i for i, t in enumerate(v)) for r in roots]
                expected = (sum(values), sum(x*y for x, y in combinations(values, 2)),
                            values[0]*values[1]*values[2])
                self.assertEqual(characteristic(f, v), expected)
                self.assertEqual([sum(t*r**i for i, t in enumerate(multiply_by_alpha(f, v))) for r in roots],
                                 [r*v for r, v in zip(roots, values)])

    def test_distinct_places_and_public_full_dependency(self):
        n = 1915966849
        work = Counter()
        m, f, _ = select_polynomial(n, work)
        rows = collect(m, f, primitive_rows(80, 16), work)
        places = character_places(f, work)
        self.assertEqual(len({p for p, _ in places}), 8)
        for p, t in places:
            self.assertGreater(p, BOUND)
            self.assertEqual(evaluate(f, t) % p, 0)
            self.assertTrue(all((a+b*t) % p for a, b, *_ in rows))
        words = [character_word(row, places, work) for row in rows]
        self.assertEqual([len(kernels(rows, words, k)) for k in (0, 4, 8)], [9, 5, 1])
        mask, = kernels(rows, words, 8)
        result, witness = check_subset(n, m, f, rows, mask)
        self.assertEqual(result['proper_divisors'], [36151, 52999])
        self.assertEqual(len(witness['rows']), 28)
        self.assertEqual(len(result['witnesses']), 1)
        self.assertEqual(result['status'], 'square_witness')

    def test_caps_and_empty_kernels(self):
        uncapped = search(989, trace_cap=5)
        zero = search(989, trace_cap=0)
        for arm, capped in zip(uncapped['arms'], zero['arms']):
            self.assertEqual(arm['kernel_dimension'], capped['kernel_dimension'])
            self.assertEqual(int(arm['remaining_dependencies'])+5, int(capped['remaining_dependencies']))
            self.assertEqual(capped['tested'], 0)
            self.assertIsNone(capped['first_hit'])
        empty = search(1734799141)
        self.assertEqual(empty['status'], 'no_norm_dependency')
        self.assertEqual(empty['remaining_cofactor'], '1734799141')
        self.assertEqual(empty['work']['euler_criterion_powers'], 0)
        self.assertEqual(empty['available_character_places'], [])
        self.assertTrue(all(a['tested'] == 0 for a in empty['arms']))
        with self.assertRaises(ValueError):
            search(3, trace_cap=-1)


if __name__ == '__main__':
    unittest.main()
