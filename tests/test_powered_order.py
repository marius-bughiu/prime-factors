import unittest
from collections import Counter
from math import gcd, isqrt, lcm

from experiments.powered_order import bounded_order, merge_orders, search, square_divisors


def direct_order(unit, modulus):
    power = unit % modulus
    order = 1
    while power != 1:
        power = power * unit % modulus
        order += 1
    return order


class PoweredOrderTests(unittest.TestCase):
    def test_bounded_order_against_sequential_powers(self):
        for n in range(3, 75):
            for base in range(1, n):
                if gcd(n, base) != 1:
                    continue
                exact = direct_order(base, n)
                for span in {1, 2, 3, 4, 5, max(1, exact-1), exact, exact+1, 25, 26}:
                    self.assertEqual(bounded_order(base, n, span, Counter()),
                                     exact if exact <= span else None)

    def test_primary_merge_retains_a_lift_of_exact_lcm(self):
        for n, m in ((55, 3), (77, 2), (1189, 7), (3363121, 15)):
            components = {}
            beta, merged = 1, 1
            for base in range(2, 12):
                if gcd(base, n) != 1:
                    continue
                order = direct_order(pow(base, m*m, n), n)
                expected = lcm(merged, order)
                beta, merged = merge_orders(n, beta, merged, components, base, order, Counter())
                self.assertEqual(merged, expected)
                self.assertEqual(direct_order(pow(beta, m*m, n), n), expected)

    def test_single_and_merged_local_certificates(self):
        for p, q, m, span, cap, method in ((10007, 15013, 15, 181, 3, "single_base"),
                                           (1297, 2593, 15, 100, 5, "lcm_merge")):
            result = search(p*q, m, span, cap, 7, 0)
            self.assertEqual((result["status"], result["method"]), ("certified_base", method))
            self.assertEqual(pow(result["beta"], m*m, p*q), result["alpha"])
            self.assertEqual(result["work"]["certificate_gcds"], span)
            for prime in (p, q):
                self.assertGreater(direct_order(result["alpha"] % prime, prime), span)
            if method == "lcm_merge":
                self.assertEqual([step["base_powered_order"] for step in result["lcm_updates"]],
                                 [72, 32])
                self.assertEqual((result["beta"], result["small_order_lcm"]), (1280, 288))

    def test_local_order_factor_from_single_and_merged_elements(self):
        for args, source in (((323, 3, 2, 8, 5, 100), "single_base"),
                             ((1189, 7, 20, 8, 5, 100), "lcm_merge")):
            result = search(*args)
            self.assertEqual((result["status"], result["method"], result["base_source"]),
                             ("factor", "local_order_gcd", source))
            n, m, span = args[:3]
            self.assertEqual(pow(result["beta"], m*m, n), result["alpha"])
            self.assertGreater(direct_order(result["alpha"], n), span)
            exponent = result["certificate_exponent"]
            self.assertTrue(1 <= exponent <= span)
            witness = gcd(pow(result["alpha"], exponent, n)-1, n)
            self.assertTrue(1 < witness < n)
            self.assertEqual(result["factor"]*result["cofactor"], n)

    def test_balanced_progression_recovery_and_budgets(self):
        self.assertEqual(square_divisors(12, Counter()),
                         sorted((d for d in range(1, 145) if 144 % d == 0), reverse=True))
        n = 10403
        args = (n, 5, 1000, 3, 5)
        for cap in (0, 1):
            result = search(*args, cap)
            self.assertEqual((result["status"], result["method"]), ("unresolved", "fallback_budget"))
            self.assertEqual(result["work"]["progression_gcds"], cap)
        hit = search(*args, 2)
        self.assertEqual((hit["factor"], hit["cofactor"], hit["progression_modulus"],
                          hit["progression_candidate"]), (101, 103, 25, 101))
        self.assertEqual(hit["work"]["progression_gcds"], 2)
        self.assertEqual(search(n, 5, 1000, 3, 26, 20)["method"], "fallback_exhausted")
        for p, q, m in ((17, 31, 2), (19, 23, 3), (29, 43, 7), (37, 67, 6)):
            n = p*q
            threshold = gcd(p-1, m*m)
            result = search(n, m, n, 1, threshold, 2*isqrt(n))
            self.assertEqual(result["method"], "divisor_progression")
            self.assertEqual(result["factor"], p)

    def test_nonunits_and_parameter_checks(self):
        self.assertEqual(search(35, 5, 5, 6, 2, 0)["method"], "modulus_gcd")
        self.assertEqual(search(35, 6, 40, 6, 2, 0)["method"], "base_gcd")
        for case in ((2, 1, 1, 1, 1, 0), (35, 0, 1, 1, 1, 0), (35, 1, 0, 1, 1, 0),
                     (35, 1, 1, 35, 1, 0), (35, 1, 1, 1, 0, 0), (35, 1, 1, 1, 1, -1)):
            with self.assertRaises(ValueError):
                search(*case)
