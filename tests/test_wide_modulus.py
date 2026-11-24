import random
import unittest
from collections import Counter

from experiments.wide_modulus import collision, search, values_at


class WideModulusTests(unittest.TestCase):
    def test_monic_remainders_over_composite_moduli(self):
        rng = random.Random(20261125)
        for n in (15, 77, 2**40+15):
            for size in range(1, 19):
                coefficients = [rng.randrange(n) for _ in range(2*size+1)]
                points = [rng.randrange(n) for _ in range(size)] + [1, 1]
                expected = [sum(c*pow(x, i, n) for i, c in enumerate(coefficients)) % n
                            for x in points]
                self.assertEqual(values_at(coefficients, points, n), expected)

    def test_composite_gcd_refines_and_exact_metadata_is_retained(self):
        work = Counter()
        result = collision(35, 2, 1, [0], [(6, 1, 1, 0, 0, 0), (8, 1, 1, 0, 0, 0)], work)
        self.assertEqual(result, (5, 'polynomial_collision'))
        self.assertEqual(work['refinement_gcds'], 1)
        # Two equal giant values carry different candidate sums. The second is true.
        result = collision(35, 2, 1, [0], [(1, 1, 1, 0, 0, 0), (1, 1, 1, 12, 0, 0)], work)
        self.assertEqual(result, (5, 'exact_trace'))

    def test_sieve_modulus_can_itself_split_the_product(self):
        hit = search(77, 14, [7], 4, 3, 4, 0)
        self.assertEqual((hit['factor'], hit['order']['method']), (7, 'modulus_gcd'))

    def test_rare_row_search_pays_for_all_chunks(self):
        params = (150235091, 105, [3, 5, 7], 4, 12, 8, 50)
        missed = search(*params, run_exceptional=False)
        self.assertIsNone(missed['factor'])
        hit = search(*params)
        self.assertEqual(hit['factor'], 10007)
        self.assertEqual(hit['exceptional_giants'], 24)
        self.assertEqual(hit['exceptional_chunk'], 61)
        self.assertEqual(hit['work']['giant_powers'], 96)
        self.assertEqual(hit['work']['points_evaluated'], 271)
