import unittest
from math import gcd

from experiments.reciprocal_anchor import candidate_cap, find_anchor, jacobi, oriented


class ReciprocalAnchorTest(unittest.TestCase):
    def test_adaptive_sign_on_composite_and_repeated_prime_powers(self):
        for d, e in [(15, 1), (119, 72), (135, 7), (343, 9)]:
            n = e*e % d
            ordinary = set()
            positive = set()
            for x in range(d):
                if gcd(x, d) != 1:
                    continue
                s = (x+n*pow(x, -1, d)) % d
                ordinary.add(s)
                if jacobi(x, d) == 1:
                    positive.add(s)
            accepted = {s for s in range(d) if oriented(s, d, e)}
            self.assertEqual(accepted & ordinary, positive)
            self.assertEqual(2*len(accepted), d-1)
            self.assertEqual(2*len(positive), len(ordinary))
        self.assertFalse(oriented(59, 119, 72))
        self.assertTrue(oriented(60, 119, 72))

    def test_root_receipts_after_square_removal(self):
        n = 137649271
        anchor = find_anchor(n, 128)
        d = anchor['period']
        self.assertEqual((d, anchor['removed_square_root']), (119, 5))
        self.assertEqual((anchor['minus_root']**2+d) % n, 0)
        self.assertEqual((anchor['root']**2-n) % d, 0)

    def test_setup_returns_a_discovered_factor(self):
        found = find_anchor(135229, 128)
        self.assertEqual(found['setup_factor'], 271)

    def test_tail_counts_positions_and_caps_residues(self):
        self.assertEqual(candidate_cap([(7,0),(8,8),(9,5)], 7, 3), 7)
