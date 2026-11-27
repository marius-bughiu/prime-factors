import unittest
from collections import Counter
from itertools import combinations
from math import gcd
from random import Random

from experiments.twelve_residue_collision import (
    directions, keys, mask, refine_duplicates, regular_samples, search, search_values,
)


def rational_key(x, p):
    numerator = x**6 - 45*x**4 + 135*x*x - 27
    return numerator**2 * pow((x*x + 3)**6, -1, p) % p


def signed_images(x, p):
    return [sign * a * pow(b, -1, p) % p
            for a, b in directions(x) for sign in (1, -1)]


def proper_pair_exists(p, q, draws, seed, mode):
    n = p*q
    rng = Random(seed)
    samples = [rng.randrange(n) for _ in range(draws)]
    if mode in ('matched', 'twelve'):
        for x in samples:
            if (mask(x, p) == 0) != (mask(x, q) == 0):
                return True
        samples = [x for x in samples if mask(x, p) and mask(x, q)]
    for x, y in combinations(samples, 2):
        if mode == 'twelve':
            at_p = signed_images(x, p)
            at_q = signed_images(x, q)
            p_hit, q_hit = y % p in at_p, y % q in at_q
            if p_hit and q_hit and at_p.index(y % p) != at_q.index(y % q):
                return True
        elif mode == 'power':
            p_hit = pow(x, 12, p) == pow(y, 12, p)
            q_hit = pow(x, 12, q) == pow(y, 12, q)
        else:
            p_hit, q_hit = (x-y) % p == 0, (x-y) % q == 0
        if p_hit != q_hit:
            return True
    return False


class TwelveResidueCollisionTests(unittest.TestCase):
    def test_all_regular_fibers_match_the_twelve_signed_images(self):
        for p in (1009, 1013, 1019):
            xs = [x for x in range(p) if mask(x, p)]
            values = keys(xs, p)
            self.assertEqual(values, [rational_key(x, p) for x in xs])
            self.assertEqual(set(Counter(values).values()), {12})
            fibers = {}
            for x, key in zip(xs, values):
                fibers.setdefault(key, set()).add(x)
            for members in fibers.values():
                self.assertEqual(set(signed_images(min(members), p)), members)

    def test_existence_against_direct_crt_comparisons(self):
        for seed in (0, 1, 7, 19, 61, 1044):
            for mode in ('twelve', 'matched', 'raw', 'power'):
                with self.subTest(seed=seed, mode=mode):
                    p, q = 1009, 1151
                    factor, _, _ = search(p*q, 16, seed, mode)
                    self.assertEqual(factor is not None, proper_pair_exists(p, q, 16, seed, mode))
                    self.assertIn(factor, (None, p, q))

    def test_shared_key_yields_explicit_signed_gcd(self):
        n = 1009*1151
        factor, work, _ = search(n, 8, 1044, 'twelve')
        self.assertEqual(work['source'], 'shared key')
        x, y = map(int, work['witness'])
        self.assertEqual(keys([x], n), keys([y], n))
        at_p, at_q = signed_images(x, 1009), signed_images(x, 1151)
        self.assertNotEqual(at_p.index(y % 1009), at_q.index(y % 1151))
        a, b = directions(x)[work['orientation']//2]
        signed_a = a if work['orientation'] % 2 == 0 else -a
        self.assertEqual(b*y - signed_a, int(work['signed_difference']))
        self.assertEqual(gcd(b*y-signed_a, n), factor)
        self.assertEqual(factor, 1151)
        self.assertEqual(work['derivative_values'], 0)
        self.assertEqual(work['distinct_keys'], 7)

    def test_shared_global_orientation_and_repeated_seeds(self):
        n = 1009*1151
        samples = [2, 2, n-2]
        counts = {'orientation_gcds': 0}
        self.assertIsNone(refine_duplicates(samples, keys(samples, n), n, counts))
        self.assertEqual(counts['orientation_gcds'], 12)

    def test_saturated_batches_recover_individual_witness(self):
        n = 1009*1151
        self.assertEqual(gcd(mask(1009, n)*mask(1151, n), n), n)
        work = {'setup_gcds': 0}
        self.assertEqual(regular_samples([1009,1151], n, work), (1009, []))
        self.assertEqual(work['source'], 'regularity check')
        work = {'row_gcds': 0, 'pair_gcds': 0}
        self.assertEqual(search_values([0,5,7], [0,5,7], 35, work), 5)
        self.assertEqual(work['witness'], ['0','5'])

    def test_zero_draw_budget(self):
        for mode in ('twelve', 'matched', 'raw', 'power'):
            factor, work, _ = search(1009*1151, 0, 42, mode)
            self.assertIsNone(factor)
            self.assertEqual(work['setup_gcds'] + work['derivative_values'], 0)


if __name__ == '__main__':
    unittest.main()
