import unittest
from collections import Counter
from math import gcd

from experiments.exceptional_weights import crt_roots, root_table, search_product


class ExceptionalWeightTests(unittest.TestCase):
    def test_crt_and_stationary_trace_on_every_lift(self):
        for r in (1, 3, 5, 6, 15, 30):
            tables = [(ell, root_table(ell)) for ell in (2, 3, 5) if r % ell == 0]
            for n in (77, 101):
                for u, v in ((1, 1), (7, 1), (1, 11)):
                    roots = sorted(crt_roots(n, u, v, tables, Counter()))
                    expected = [s for s in range(r) if (v*s*s-u*n) % r == 0]
                    self.assertEqual(roots, expected)
                    for s in roots:
                        residues = {(u*n*pow(x, -1, r*r)+v*x) % (r*r)
                                    for x in range(s, r*r, r)}
                        self.assertEqual(len(residues), 1)

    def test_41_bit_prime_pair(self):
        result = search_product(1900014700027, 330, 10, 20, 40)
        self.assertEqual((result["direct"]["factor"], result["power"]["cofactor"]),
                         (1000003, 1900009))
        self.assertEqual((result["power"]["u"], result["power"]["v"],
                          result["power"]["trace"], result["power"]["kind"]),
                         (10, 19, 38000147, "proper_gcd"))
        # A reduced-basis certificate for the correct Harvey–Hittmeir cell,
        # identified using the factors only after the product-only search.
        n = 1900014700027
        p = result["direct"]["factor"]
        sigma = p % 330
        cell = 1
        while (331*cell+329)//330 <= p:
            cell = (331*cell+329)//330
        self.assertEqual((sigma, cell), (103, 997245))
        first, second = (100, 190), (203, 389)
        for a, b in (first, second):
            self.assertEqual((b*sigma*sigma-a*n) % 330, 0)
        self.assertEqual(abs(first[0]*second[1]-first[1]*second[0]), 330)
        def transform(a, b):
            return (n*a, 330*(cell*cell*b-n*a))
        x, y = transform(*first), transform(*second)
        norm_x, norm_y = sum(c*c for c in x), sum(c*c for c in y)
        self.assertLessEqual(2*abs(x[0]*y[0]+x[1]*y[1]), norm_x)
        self.assertLessEqual(norm_x, norm_y)
        self.assertEqual(gcd(gcd(*first), 330), 10)
        work = result["work"]
        self.assertEqual((work["weight_pairs"], work["roots"], work["traces"],
                          work["giants"], work["pair_gcds"]), (400, 172, 2, 2, 2))
        cutoff = search_product(1900014700027, 330, 10, 20, 32)
        self.assertIsNone(cutoff["direct"])
        self.assertIsNone(cutoff["power"])

    def test_true_hits_and_misses_all_small_pairs(self):
        primes = (11, 13, 17, 19, 23, 29, 31)
        for j, p in enumerate(primes):
            for q in primes[j+1:]:
                if q > 2*p:
                    continue
                n = p*q
                for r in (1, 3, 5, 15):
                    for gap in (2, 11, 25):
                        result = search_product(n, 15, 15//r, 3, gap, 3)
                        model = any(
                            gcd(u*v, r) == 1 and abs(u*y-v*x) <= gap
                            and (v*x*x-u*n) % r == 0
                            for x, y in ((p, q), (q, p))
                            for u in range(1, 4) for v in range(1, 4))
                        with self.subTest(n=n, r=r, gap=gap):
                            self.assertEqual(result["direct"] is not None, model)
                            if model:
                                self.assertEqual(result["power"]["factor"], p)
                            if result["power"]:
                                self.assertEqual(result["power"]["cofactor"], q)
                            self.assertLessEqual(result["work"]["traces"],
                                                 result["work"]["unfiltered_traces"])

    def test_short_order_and_incidental_collision(self):
        result = search_product(15049, 30, 6, 4, 300, 4, 1)
        self.assertEqual(result["power"]["kind"], "exact")
        self.assertEqual(result["work"]["exact_match_square_tests"], 50)
        self.assertEqual(result["work"]["giants"], 18)
        incidental = search_product(34387, 30, 6, 5, 150, 4)
        self.assertIsNone(incidental["direct"])
        self.assertEqual((incidental["power"]["factor"], incidental["power"]["trace"]),
                         (137, 539))

    def test_invalid_bounds(self):
        for args in [(35, 9, 3, 4, 20), (35, 6, 4, 4, 20), (35, 6, 3, 0, 20),
                     (35, 10, 5, 4, 20), (35, 6, 3, 4, 20, 3, 7)]:
            with self.assertRaises(ValueError):
                search_product(*args)
