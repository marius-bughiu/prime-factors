from math import gcd, prod
import unittest
from unittest.mock import patch

from experiments.character_divisor_column import DISCRIMINANTS, search
from experiments.factorial_progressions import search as existing_forward
from experiments.mixed_ratio_heights import jacobi
from experiments.short_pascal_row import interval


class CharacterColumnTests(unittest.TestCase):
    def test_literal_column_and_signed_denominator_periods(self):
        for n in (19*23, 59*61, 79*107, 193*251, 251*223, 1009*1019):
            for d in DISCRIMINANTS + (6, -10, 15):
                if jacobi(d,n) != -1:
                    continue
                for wheel in (2, 30):
                    for clip in (False, True):
                        run = search(n, discriminants=(d,), wheel=wheel, clip=clip)
                        lo, hi = int(run['lower']), int(run['upper'])
                        selected = [j for j in range(lo,hi+1) if j%2 and gcd(j,wheel)==1
                                    and jacobi(d,j)==run['sign']]
                        self.assertEqual(int(run['candidates']), len(selected))
                        self.assertLessEqual(len(selected), int(run['other_candidates']))
                        if run['outcome'] == 'interpolation_divisor':
                            self.assertTrue(1 < run['factor'] < n and n%run['factor']==0)
                        else:
                            self.assertEqual(int(run['product']),prod(selected)%n)
                            self.assertEqual(int(run['unvisited']),0)
                            self.assertEqual(run['factor'],gcd(prod(selected),n))

    def test_matched_backend(self):
        for n in (19*23, 79*107, 1009*1019, 10007*12301, 62141*47189):
            base = existing_forward(n,None,wheel=30,equal_width=True)
            same = search(n,ordinary=True)
            self.assertEqual(base['factor'],same['factor'])
            self.assertEqual(base['product'],same['product'])
            self.assertEqual(base['work'].get('convolution_input_coefficients',0),
                             same['work'].get('convolution_input_coefficients',0))

    def test_lower_and_upper_partner_bounds(self):
        for p,q in ((19,23),(79,107),(193,251),(1009,1019)):
            n=p*q
            for clip in (False, True):
                run=search(n,wheel=2,clip=clip)
                self.assertEqual(run['outcome'],'column_gcd')
                self.assertIn(run['factor'],(p,q))
                if clip:
                    self.assertEqual(int(run['lower']),interval(n)[0])
                    self.assertGreaterEqual(int(run['upper']),q)

    def test_matched_period_bound_over_complete_small_population(self):
        primes = (67,71,73,79,83,89,97,101,103,107,109,113,127)
        for i,p in enumerate(primes):
            for q in primes[i+1:]:
                n=p*q
                if n.bit_length()!=14:
                    continue
                for d in (-1,2,3,5,7,11):
                    if jacobi(d,n)!=-1:
                        continue
                    run=search(n,discriminants=(d,),wheel=2,clip=True,max_work=0)
                    lo,root=interval(n)
                    direct=sum(gcd(v,run['period'])==1 for v in range(lo,root+1))
                    self.assertEqual(int(run['matched_interval_candidates']),direct)
                    self.assertGreaterEqual(int(run['candidates'])+run['matched_period_residues'],direct)

    def test_cap_stops_before_polynomials(self):
        n=10007*12301
        full=search(n,wheel=2)
        self.assertIsNotNone(full['factor'])
        with patch('experiments.character_divisor_column.block_products',side_effect=AssertionError):
            stopped=search(n,wheel=2,max_work=int(full['planned_block_work'])-1)
            self.assertEqual(stopped['outcome'],'work_limit')
            self.assertEqual(stopped['unvisited'],stopped['candidates'])
            self.assertEqual(stopped['visited'],'0')
            self.assertEqual(stopped['work'],{})
        self.assertEqual(search(n,wheel=2,max_work=int(full['planned_block_work']))['factor'],full['factor'])

    def test_no_witness_and_independent_selector_factor(self):
        self.assertEqual(search(13*17,wheel=2,discriminants=(-1,))['outcome'],'no_witness')
        self.assertEqual(search(13*17,wheel=2,discriminants=(13,))['factor'],13)
        self.assertEqual(search(7*11,wheel=14)['outcome'],'wheel_divisor')


if __name__=='__main__':
    unittest.main()
