import unittest
from itertools import product
from math import gcd, isqrt

from experiments.sum_signature_join import _incremental_entries, _moduli, search


class SumSignatureJoinTests(unittest.TestCase):
    def test_bounded_counts_match_direct_enumeration(self):
        for n in range(9, 600, 2):
            first = isqrt(4*n)
            first += first*first != 4*n
            last = isqrt(9*n//2)
            for bases in ((1, 1), (2,), (n-1, 2)):
                result = search(n, bases=bases)
                work = result["work"]
                if work["signature_matches"] is None:
                    for factor in result["factors"]:
                        self.assertEqual(n % int(factor), 0)
                    continue
                masks = []
                period = 1
                moduli = _moduli()
                while period < work["period"]:
                    m = next(moduli)
                    masks.append((m, {(x+n*pow(x, -1, m)) % m
                                      for x in range(1, m) if gcd(x, m) == 1}))
                    period *= m
                direct = [s for s in range(first, last+1)
                          if all(s % m in residues for m, residues in masks)]
                hits = [s for s in direct if all(pow(g, s, n) == pow(g, n+1, n) for g in bases)]
                self.assertEqual(work["raw_interval_survivors"], len(direct))
                self.assertEqual(work["signature_matches"], len(hits))
                if result["factors"]:
                    p, q = map(int, result["factors"])
                    self.assertEqual(p*q, n)
                    if len(hits) == 1:
                        self.assertEqual(p+q, hits[0])

    def test_fresh_recovery_and_cap(self):
        n = 2961805344422983
        found = search(n)
        self.assertEqual(found["factors"], ["52902449", "55986167"])
        self.assertEqual(found["work"]["signature_matches"], 1)
        ambiguous = search(n, bases=(1, 1))
        self.assertEqual(ambiguous["outcome"], "ambiguous_signature")
        self.assertEqual(ambiguous["work"]["signature_matches"], 15902)
        capped = search(n, max_half_entries=215)
        self.assertEqual(capped["outcome"], "half_list_limit")
        self.assertEqual(capped["work"]["unvisited_half_entries"], 432)
        self.assertEqual(capped["work"]["modular_powers"], 0)

    def test_two_matching_sums_give_a_factor(self):
        n = 109969
        result = search(n, bases=(35,))
        self.assertEqual(result["factors"], ["277", "397"])
        work = result["work"]
        self.assertEqual(work["signature_matches"], 2)
        self.assertEqual(work["aggregate_exponent"], "218580")
        self.assertEqual((work["halving_squares"], work["halving_gcds"]), (1, 2))
        self.assertEqual(work["square_tests"], 0)

    def test_incremental_updates_include_both_wrap_directions(self):
        n, period = 143, 12
        bases = (2, 5)
        groups = [[0], [0, 8], [5, 7], [0, 9, 11]]

        def signature(value):
            return tuple(pow(g, value, n) for g in bases)

        def multiply(a, b):
            return tuple(x*y % n for x, y in zip(a, b))

        for sign, start in ((1, 0), (-1, 23)):
            entries = _incremental_entries(groups, period, signature(start), sign == -1,
                                           signature, multiply, signature(-period), {"digit_powers": 0})
            residues = [sum(digits) % period for digits in product(*groups)]
            expected = [(r, signature(start+sign*r)) for r in residues]
            self.assertEqual(sorted(entries), sorted(expected))

    def test_search_matches_direct_counts_and_charges_updates(self):
        n = 2961805344422983
        for value, bases, cap in ((n, (3,), 65536), (n, (1, 1), 65536), (n, (3,), 215),
                                  (109969, (35,), 65536), (9, (2,), 1)):
            args = {"bases": bases, "max_half_entries": cap}
            direct = search(value, **args)
            updated = search(value, incremental=True, **args)
            self.assertEqual(direct["outcome"], updated["outcome"])
            self.assertEqual(direct["factors"], updated["factors"])
            for key in direct["work"].keys() - {
                    "digit_powers", "signature_multiplications", "modular_powers", "signature_inversions"}:
                self.assertEqual(direct["work"][key], updated["work"][key], key)
            if cap == 215:
                for key in ("digit_powers", "signature_multiplications", "signature_inversions", "crt_inverses"):
                    self.assertEqual(updated["work"][key], 0, key)
            if value == n and bases == (3,) and cap == 65536:
                self.assertEqual(direct["work"]["modular_powers"], 433)
                self.assertEqual(updated["work"]["modular_powers"], 39)
                self.assertEqual(updated["work"]["signature_inversions"], 1)
                self.assertGreater(updated["work"]["signature_multiplications"],
                                   direct["work"]["signature_multiplications"])
