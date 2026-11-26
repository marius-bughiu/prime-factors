import unittest

from experiments.multiplier_block_moments import (
    SCALE, compare, direct_divisions, intersection_count, moments, residue_lanes,
)


class MultiplierBlockMomentTests(unittest.TestCase):
    def test_compatible_incompatible_and_truncated_intersections(self):
        for left_mod, right_mod in ((3, 5), (4, 8), (6, 9), (7, 7)):
            for left in range(left_mod):
                for right in range(right_mod):
                    for width in (0, 1, 12, 40):
                        actual = intersection_count((left, left_mod, 3), (right, right_mod, -2), width)
                        expected = sum(i % left_mod == left and i % right_mod == right for i in range(width))
                        self.assertEqual(actual, expected)

    def test_shifted_quadratics_and_repeated_coefficient_prime(self):
        # The discriminants B²−AC are 10403 and 3*10403. Both square coefficients
        # have exactly one root at 13 and 13². Finite scores charge both levels.
        baseline, candidate = (169, 56, -43), (169, 36, -177)
        primes = (2, 3, 5, 7, 11, 13)
        radius, limit = 47, 200
        baseline_roots, _ = residue_lanes(baseline, primes, radius, limit)
        candidate_roots, _ = residue_lanes(candidate, primes, radius, limit)
        for roots in (baseline_roots, candidate_roots):
            for q in (13, 169):
                self.assertEqual(sum(modulus == q for _, modulus, _ in roots), 1)
        signed = candidate_roots + [(r, m, -w) for r, m, w in baseline_roots]
        _, before, _ = direct_divisions(baseline, primes, radius, limit)
        _, after, _ = direct_divisions(candidate, primes, radius, limit)
        differences = [y - x for x, y in zip(before, after)]
        self.assertEqual(moments(signed, 2 * radius + 1), (sum(differences), sum(d*d for d in differences)))

    def test_full_smoothness_and_strict_price_comparisons(self):
        # 2^8 is smooth even when only the first two levels are scored.
        self.assertEqual(direct_divisions((0, 0, -256), (2,), 1, 4), ([256]*3, [2*SCALE]*3, 3))
        run = compare(10403, k=1, prime_bound=13, max_power=49, radius=8)
        for field in ('gain_sum', 'squared_gain_sum', 'classical_price_wins', 'actual_price_wins'):
            self.assertEqual(run[field], 0)
        self.assertEqual(run['mean_actual_price_bits'], 0)
        with self.assertRaises(ValueError):
            direct_divisions((1, 0, 0), (2,), 2, 4)


if __name__ == '__main__':
    unittest.main()
