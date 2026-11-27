import json
from math import gcd, prod
from pathlib import Path
import unittest

from experiments.reduced_smooth_readout import blocks, ordinary_sweep, search
from scripts.factor import primes_through


class ReducedSmoothReadout(unittest.TestCase):
    def test_full_powers_and_truncation(self):
        self.assertEqual(list(blocks(13, 3)), [(2, 4), (3, 3), (5, 5), (7, 7)])
        self.assertEqual(list(blocks(2, 1)), [])
        self.assertEqual(list(blocks(3, 5)), [(2, 16), (3, 27)])

    def test_setup_and_readout_branches(self):
        factor, work = search(341, 3, 5, 2)
        self.assertIsNone(factor)
        self.assertEqual(work['source'], 'base budget exhausted')
        self.assertEqual(work['readout_gcds'], 0)
        factor, work = search(341, 3, 5, 3)
        self.assertEqual((factor, work['source'], work['accepted_base']), (11, 'before identity', 3))
        self.assertEqual((work['base_gcds'], work['readout_gcds']), (2, 1))
        self.assertEqual(search(6, 2, 2, 2)[0], 2)
        self.assertEqual(search(47*59, 13, 6, 2)[1]['source'], 'smoothness sweep exhausted')

    def test_first_accepted_base_against_projected_orders(self):
        primes = primes_through(120)
        for j, q in enumerate(primes):
            for p in primes[1:j]:
                n, bits, g = p*q, q.bit_length(), gcd(p-1, q-1)
                for bound in (2, 3, 5, 7, 13):
                    factor, work = search(n, bound, bits, 12)
                    if work['accepted_base'] is None:
                        self.assertIn(factor, (p, q, None))
                        continue
                    self.assertEqual(work['readout_gcds'], 1)
                    e = prod(power for _, power in blocks(bound, bits))
                    a = work['accepted_base']
                    split = pow(a, (n-1)*e, p) == 1 or pow(a, (n-1)*e, q) == 1
                    self.assertEqual(split, factor is not None)
                    if split:
                        self.assertIn(factor, (p, q))
                    else:
                        self.assertNotEqual(e % ((p-1)//g), 0)
                        self.assertNotEqual(e % ((q-1)//g), 0)

    def test_exact_uniform_unit_probability(self):
        for p, q, bound in ((11, 31, 2), (13, 19, 3), (31, 43, 2), (23, 47, 5)):
            n, g = p*q, gcd(p-1, q-1)
            r, s = (p-1)//g, (q-1)//g
            e = prod(power for _, power in blocks(bound, q.bit_length()))
            u, v = gcd(r,e), gcd(s,e)
            accepted = successes = 0
            for a in range(1, n):
                if gcd(a,n) > 1 or pow(a,n-1,n) == 1:
                    continue
                accepted += 1
                successes += pow(a,(n-1)*e,p) == 1 or pow(a,(n-1)*e,q) == 1
            self.assertEqual(accepted, g*g*(r*s-1))
            self.assertEqual(successes, g*g*(u*s+v*r-u*v-1))

    def test_ordinary_refines_saturated_checkpoint(self):
        factor, work = ordinary_sweep(3*5, 2, 2, 3)
        self.assertEqual((factor, work['saturated'], work['refinement_powers']), (3, True, 1))
        self.assertEqual((work['blocks'], work['gcds']), (1, 2))

    def test_full_size_inputs(self):
        path = Path(__file__).resolve().parents[1] / 'benchmarks/reduced-smooth-readout.json'
        for case in json.loads(path.read_text()):
            n = int(case['n'])
            factor, work = search(n, case['bound'], case['factor_bits'], case['base_limit'])
            self.assertEqual(n.bit_length(), 2048)
            for field, expected in case['checks'].items():
                self.assertEqual(work[field], expected)
            self.assertEqual(sorted([str(factor), str(n//factor)], key=int) if factor else [], case['factors'])
            other, classical = ordinary_sweep(n, work['accepted_base'], case['bound'], case['factor_bits'])
            self.assertIsNone(other)
            self.assertEqual(classical['blocks'], case['ordinary']['blocks'])
            self.assertEqual(classical['gcds'], case['ordinary']['gcds'])
