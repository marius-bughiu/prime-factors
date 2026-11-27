import json
import unittest

from experiments.affine_radix_holdout import draw_prime
from experiments.power_denominator_census import LONG_POWER, ROOT, diagnostic, probe, run_fixture


class PowerDenominatorCensus(unittest.TestCase):
    def test_existing_independent_draw_and_public_rejection(self):
        cases = json.loads((ROOT/"benchmarks/power-ratio-remainder.json").read_text())
        p,q = [draw_prime(s,7,bits=11,seed=b'local-gap-polynomial-v1/11') for s in (b'p',b'q')]
        self.assertEqual(p*q,int(cases[0]["n"]))
        for case in cases:
            args = {k:case[k] for k in ("n","factor_bits","exponent_rule","exponent") if k in case}
            outcome = run_fixture(args)
            self.assertEqual(outcome,case["checks"])
            self.assertEqual(outcome["pair"],case["factors"])
        self.assertEqual(cases[0]["checks"]["witness"]["denominator"],"43")
        self.assertEqual(cases[1]["checks"]["convergents"],0)

    def test_exact_dyadic_endpoints(self):
        # 323 = 17 × 19, both five-bit primes. The two exponents generate
        # a false candidate of deficit exactly 32 and another exactly 64.
        self.assertEqual(probe(323,194,factor_bits=5)["width_survivors"],1)
        self.assertEqual(probe(323,259,factor_bits=5)["width_survivors"],0)

    def test_stopping_at_first_upper_deficit_below_width(self):
        counted = 0
        for n,k in ((143,4),(323,5),(899,5)):
            for e in range(1,n+1):
                full = probe(n,e,gate=False,factor_bits=k)
                cut = probe(n,e,gate=False,factor_bits=k,early_stop=True)
                for key in ("pair","square_tests","width_survivors","witness"):
                    self.assertEqual(full[key],cut[key],(n,e,key))
                self.assertLessEqual(cut["convergents"],full["convergents"])
                if cut["stopped_early"]:
                    counted += 1
                    self.assertLess(cut["convergents"],full["convergents"])
        self.assertGreater(counted,0)
        self.assertFalse(probe(323,323,gate=False,factor_bits=5,early_stop=True)["stopped_early"])
        self.assertFalse(probe(323,1,factor_bits=5,early_stop=True)["stopped_early"])

    def test_nontrivial_powered_images(self):
        row = diagnostic(1051,1249,LONG_POWER)
        self.assertEqual(row["image_sizes"],[5,2])
        self.assertEqual((row["numerator"],row["denominator"]), (11,20))
        self.assertTrue(row["hit"] and row["exact"] and row["remainder_gate"])
        self.assertFalse(row["uniform"])

    def test_width_band_and_complete_totient_probe(self):
        n=2585873
        self.assertEqual(probe(n,LONG_POWER)["square_tests"],3)
        result=probe(n,LONG_POWER,factor_bits=11)
        self.assertEqual(result["square_tests"],1)
        self.assertEqual(result["pair"],["1291","2003"])
        for e in (1,n-1,(n-1)//2,840):
            self.assertFalse(probe(n,e)["passed"])
            self.assertEqual(probe(n,e,gate=False)["square_tests"],0)
