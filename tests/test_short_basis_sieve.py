import unittest
from collections import Counter
from math import gcd, isqrt

from experiments.short_basis_sieve import first_vector, recover_trace, search, setup


class ShortBasisSieveTests(unittest.TestCase):
    def test_gauss_minimality_by_bounded_exhaustion(self):
        n, m, m0 = 5459, 15, 3
        for anchor in (53, 71):
            def norm(a, b):
                return (n*a)**2 + (m0*(anchor**2*b-n*a))**2

            for sigma in (1, 2, 4, 7, 8, 11, 13, 14):
                a, b = first_vector(n, m, m0, sigma, anchor, Counter())
                self.assertEqual((b*sigma*sigma-a*n) % m, 0)
                radius = isqrt(norm(a, b))
                # Any shorter vector must satisfy both coordinate inequalities.
                for c in range(-radius//n, radius//n+1):
                    limit = (radius//m0+n*abs(c))//(anchor*anchor)
                    for d in range(-limit, limit+1):
                        if (c or d) and (d*sigma*sigma-c*n) % m == 0:
                            self.assertGreaterEqual(norm(c, d), norm(a, b))

    def test_true_trace_survives_local_rules(self):
        primes = (17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71)
        for p in primes:
            for q in primes:
                if not p < q <= 2*p:
                    continue
                for m, m0, selected, max_bad in ((1, 3, [], 0), (15, 3, [3, 5], 0),
                                                 (21, 7, [3, 7], 1), (30, 3, [3, 5], 1)):
                    n = p*q
                    giants, radius, period, allowed, _ = setup(n, m, m0, selected, max_bad)
                    matched = [g for g in giants
                               if g.anchor <= p <= g.upper and (g.sigma-p) % m == 0]
                    self.assertEqual(len(matched), 1)
                    g = matched[0]
                    trace = g.a*q+g.b*p
                    i, rem = divmod(trace-g.offset, m*m)
                    self.assertEqual(rem, 0)
                    self.assertLessEqual(0, i)
                    self.assertLessEqual(i, 2*radius)
                    self.assertEqual(gcd(g.a, m), g.d)
                    if g.bad <= max_bad:
                        self.assertIn((i+g.shift) % period, allowed)
                    self.assertEqual(recover_trace(n, g.a, g.b, trace), p)

    def test_mixed_control_needs_exceptional_branch(self):
        result = search(5459, 15, 3, [3, 5], compare=True, exceptional=True)
        self.assertEqual((result["kept"], result["skipped"]), (8, 8))
        self.assertIsNone(result["ordinary"]["first"])
        self.assertEqual(result["ordinary"]["work"]["pair_gcds"], 18)
        self.assertEqual(result["dense_retained"]["work"]["pair_gcds"], 40)
        self.assertEqual(result["coarse_all"]["work"]["pair_gcds"], 80)
        self.assertEqual(result["exceptional_budgets"], {3: (1, 6), 5: (2, 63)})
        self.assertIsNone(result["exceptional"][3]["power"])
        sweep = result["exceptional"][5]
        self.assertEqual(sweep["work"]["pair_gcds"], 6)
        for readout in (sweep["direct"], sweep["power"]):
            self.assertEqual((readout["factor"], readout["cofactor"], readout["trace"]),
                             (53, 103, 209))

    def test_tolerated_degeneracy_and_exact_collision(self):
        n = 22261
        result = search(n, 105, 4, [3, 5, 7], 1)
        hit = result["ordinary"]["first"]
        self.assertEqual((hit["factor"], hit["cofactor"], hit["kind"]), (113, 197, "exact"))
        self.assertEqual((hit["giant"]["bad"], hit["giant"]["d"], hit["giant"]["shift"]),
                         (1, 5, 95))
        self.assertEqual((hit["trace"], hit["index"], hit["baby_exponent"]), (1550, 2, 97))
        self.assertEqual(result["bad_histogram"], {0: 48, 1: 40, 2: 8})
        self.assertEqual(result["setup_work"]["crt_membership_checks"], 315)

    def test_wider_index_interval_and_short_order_base(self):
        n = 10007*15013
        result = search(n, 15, 3, [3, 5], compare=True)
        self.assertEqual((result["sparse_entries"], result["unshifted_dense_entries"]), (97, 167))
        self.assertEqual(result["ordinary"]["work"]["pair_gcds"], 1070)
        self.assertEqual(result["dense_retained"]["work"]["pair_gcds"], 2004)
        hit = result["ordinary"]["first"]
        self.assertEqual(hit["factor"]*hit["cofactor"], n)
        # All powers equal 1. Every equality must be retained for decoding.
        result = search(2491, 15, 3, [3, 5], base=1)
        hit = result["ordinary"]["first"]
        self.assertEqual((hit["factor"], hit["cofactor"], hit["kind"]), (47, 53, "exact"))

    def test_validation_and_signed_weights(self):
        for args in ((9, 3, 1, []), (17, 9, 1, []), (17, 15, 0, []),
                     (17, 15, 1, [2]), (17, 15, 1, [3, 3]), (17, 15, 1, [3], 2)):
            with self.assertRaises(ValueError):
                search(*args)
        n, p, q = 5459, 53, 103
        for a, b in ((1, -1), (-3, -2), (0, 5), (-2, 0)):
            self.assertEqual(recover_trace(n, a, b, a*q+b*p), p)
