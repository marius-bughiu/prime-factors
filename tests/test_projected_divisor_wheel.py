import unittest
from itertools import combinations
from math import isqrt, prod

from experiments.pell_pairs import convergents
from experiments.projected_divisor_wheel import BASE, PERIOD, allowed, project, run


class ProjectedDivisorWheelTest(unittest.TestCase):
    def test_projection_spans_every_supported_class_in_small_prefix(self):
        n = 5459
        relations = project(n, 12)
        values = [sign*value for _, value, sign, _, _ in convergents(n, 4, 12)]
        expected = set()
        for size in range(len(values)+1):
            for subset in combinations(values, size):
                value = prod(subset)
                mask = int(value < 0)
                value = abs(value)
                for i, p in enumerate(BASE[1:], 1):
                    while value % p == 0:
                        value //= p
                        mask ^= 1 << i
                if isqrt(value)**2 == value:
                    expected.add(mask)
        obtained = {0}
        for entry in relations['constraints']:
            self.assertEqual((int(entry['root'])**2 - entry['discriminant']) % n, 0)
            obtained |= {mask ^ entry['mask'] for mask in obtained}
        self.assertEqual(obtained, expected)
        self.assertEqual((relations['direct_rank'], relations['projected_rank']), (1, 2))
        rows = allowed(relations['constraints'])
        for divisor in (1, 53, 103, n):
            self.assertIn(divisor % PERIOD, rows)

    def test_division_budget_stops_immediately_before_the_factor(self):
        n = 741311473907
        miss = run(n, 20, 256, 2967)
        self.assertEqual((miss['factor'], miss['divisions']), (None, 2967))
        hit = run(n, 20, 256, 2968)
        self.assertEqual((hit['factor'], hit['divisions']), ('764189', 2968))
        self.assertEqual(project(n, 0)['steps'], 0)
