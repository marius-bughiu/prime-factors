import unittest
from itertools import combinations
from math import gcd, isqrt, prod

from experiments.pell_pairs import convergents
from experiments.pooled_relations import search


def brute_force_split(n, multipliers, budget):
    """Enumerate subsets of the raw rows without normalizing or discarding duplicates."""
    walks = [convergents(n, m, budget) for m in multipliers]
    rows = []
    steps = 0
    while walks and steps < budget:
        continuing = []
        for walk in walks:
            _, absolute, sign, x, center = next(walk)
            common = gcd(absolute, n)
            if 1 < common < n:
                return True
            if common == 1:
                rows.append((sign*absolute, x))
            if absolute != 1 and not center:
                continuing.append(walk)
            steps += 1
            if steps == budget:
                break
        walks = continuing
    for size in range(1, len(rows)+1):
        for subset in combinations(rows, size):
            norm = prod(row[0] for row in subset)
            if norm < 0:
                continue
            root = isqrt(norm)
            if root**2 == norm and 1 < gcd(prod(row[1] for row in subset)-root, n) < n:
                return True
    return False


class PooledRelationsTest(unittest.TestCase):
    def test_compression_preserves_all_splits_on_short_prefixes(self):
        for n in (101*107, 173*179, 211*241, 443*577, 4421*4861):
            for multipliers in ([1, 4, 9], [1, 7], [2, 5, 16]):
                for budget in (3, 6, 9):
                    with self.subTest(n=n, multipliers=multipliers, budget=budget):
                        factor = search(n, multipliers, budget)['factor']
                        self.assertEqual(factor is not None, brute_force_split(n, multipliers, budget))
                        if factor is not None:
                            self.assertEqual(n % factor, 0)
                            self.assertLess(factor, n)
                            self.assertGreater(factor, 1)

    def test_cross_walk_collision_stops_immediately(self):
        work = search(21490481, [1, 7], 10000)
        self.assertEqual((work['steps'], work['factor'], work['selected_steps']),
                         (6, 4421, [[1, 3], [7, 3]]))

    def test_budget_zero_and_multiplier_divisors(self):
        self.assertEqual(search(22, [1, 4], 0)['factor'], 2)
        self.assertIsNone(search(2, [1], 0)['factor'])
        self.assertEqual(search(77, [1, 4], 0)['steps'], 0)
        self.assertEqual(search(77, [1, 7], 4)['factor'], 7)
        with self.assertRaises(ValueError):
            search(77, [1, 1], 4)
        with self.assertRaises(ValueError):
            search(77, [77], 4)
