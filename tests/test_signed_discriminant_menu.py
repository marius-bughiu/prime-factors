from math import gcd
import unittest

from experiments.line_powers import trace_power
from experiments.signed_discriminant_menu import compare, jacobi, prime_powers, schedule, search, signs


class SignedDiscriminantMenu(unittest.TestCase):
    def test_scalar_ladder_matches_quadratic_multiplication(self):
        # Independent coordinate powering for split and nonsplit quadratic algebras.
        for prime in (7, 11, 17):
            for d in range(1, prime):
                for t in range(2, prime):
                    norm = (t*t-d) % prime
                    if norm == 0:
                        continue
                    inv = pow(norm, -1, prime)
                    a, b = (t*t+d)*inv % prime, 2*t*inv % prime
                    x, y = 1, 0
                    for e in range(20):
                        self.assertEqual(trace_power(2*a, e, prime), 2*x % prime)
                        self.assertEqual(gcd(2*x-2, prime) == prime, (x,y) == (1,0))
                        x, y = (a*x+d*b*y) % prime, (a*y+b*x) % prime

    def test_prefixes_have_equal_caps_and_distinct_discriminants(self):
        self.assertEqual(prime_powers(1), [])
        self.assertEqual(prime_powers(13), [8,9,5,7,11,13])
        for anchor in (2,7,97):
            for mode in ("menu","primes","anchored_primes"):
                for budget in range(1,26):
                    ds = schedule(mode, anchor, budget)
                    self.assertEqual(len(ds), budget)
                    self.assertEqual(len(set(ds)), budget)
        self.assertEqual(schedule("menu", 2, 8), [1,2,3,6,5,10,7,14])

    def test_real_gain_and_loss_with_missing_local_sign(self):
        for n, p, q, winner, d, checkpoint in [
            (2218279573,37619,58967,"menu",10,13),
            (2222165411,37799,58789,"primes",11,7),
        ]:
            cases = compare(n)
            self.assertEqual(p*q,n)
            hit = cases[winner]
            self.assertIn(int(hit["divisor"]), (p,q))
            self.assertEqual((hit["winner"], hit["checkpoint"]), (d, checkpoint))
            other = cases["primes" if winner == "menu" else "menu"]
            self.assertIsNone(other["divisor"])
            self.assertEqual(other["trials"], 8)
            self.assertNotIn(signs(d,p,q), {signs(v,p,q) for v in other["discriminants"]})
            for mode in ("ordinary_projected", "ordinary"):
                self.assertIsNone(cases[mode]["divisor"])
            self.assertEqual(jacobi(cases["menu"]["anchor"], n), -1)

    def test_anchor_gcd_bound_and_one_trial(self):
        d, row = search(15, "menu")
        self.assertEqual((d, row["outcome"], row["trials"]), (3, "anchor gcd", 0))
        d, row = search(101**2, "menu")
        self.assertEqual((d, row["outcome"], row["trials"]), (None, "anchor bound", 0))
        _, row = search(101*113, "menu", 1, 1)
        self.assertEqual(row["discriminants"], [1])
        self.assertEqual(row["jacobi_tests"], 0)
        with self.assertRaises(ValueError):
            search(10, "menu")
