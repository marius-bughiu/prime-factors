import json
from math import gcd, lcm
import unittest

from experiments.scaled_power_menu import ROOT, prefixes, run_fixture, search


class ScaledPowerMenuTests(unittest.TestCase):
    def test_distinct_prefixes_and_shared_modular_residues(self):
        for n in (15, 143, 10697327):
            exponents = []
            previous = 1
            for index in range(2, n+2):
                exponent = lcm(*range(1, index+1))
                if exponent > n:
                    break
                if exponent != previous:
                    exponents.append((index, exponent, exponent//previous))
                previous = exponent
            self.assertEqual(list(prefixes(n)), exponents)
            power = 2
            for _, exponent, ratio in exponents:
                power = pow(power, ratio, n)
                self.assertEqual(power, pow(2, exponent, n))

    def test_gcd_equal_to_the_input_is_a_miss(self):
        work = search(11*13, 4, compare_full=True)
        self.assertEqual(work["menu"]["eligible"], 1)
        self.assertEqual(work["modular"]["gcd_product"], 1)
        self.assertEqual(work["modular"]["pair"], [])
        self.assertEqual(work["cf"]["pair"], ["11", "13"])
        self.assertEqual(work["fermat"]["steps"], 1)

    def test_native_cases_and_complete_gcd_accounting(self):
        for case in json.loads((ROOT/"benchmarks/scaled-power-menu.json").read_text()):
            with self.subTest(case=case["id"]):
                public = {"n": case["n"], "factor_bits": case["factor_bits"]}
                work = run_fixture(public)
                self.assertEqual(work, case["checks"])
                self.assertEqual(work["pair"], case["factors"])
                modular = work["modular"]
                self.assertEqual(work["menu"]["eligible"],
                                 sum(modular[k] for k in ("gcd_one", "gcd_product", "proper_gcd")))

    def test_only_eligible_exponents_are_checked_for_gcd(self):
        n = 10697327
        work = search(n, 12)
        values = [gcd(pow(2, e, n)-1, n) for _, e, _ in prefixes(n) if (e+1)**2 >= 4*n]
        self.assertEqual(work["modular"]["gcd_one"], values.count(1))
        self.assertEqual(work["modular"]["proper_gcd"], sum(1 < v < n for v in values))
        self.assertEqual(work["modular"]["gcd_product"], values.count(n))
