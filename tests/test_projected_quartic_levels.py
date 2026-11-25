from collections import Counter
import json
from math import prod
import unittest

from experiments.affine_radix_holdout import trial_search
from experiments.gap_newton_lanes import dickson_basis
from experiments.projected_quartic_levels import ROOT, clear_column, has_local_root, primitive_level
from experiments.projected_quartic_levels import projected_basis, search, signed_class
from experiments.unit_quartic_probe import local_values
from experiments.centered_sum_quartic import windows
from experiments.projected_level_sieve import block_survivors, centered_search, covered_centered_groups, level_image


class ProjectedQuarticTests(unittest.TestCase):
    def test_projection_preserves_lifts_and_exact_determinant(self):
        for n, r, u in ((77, 8, 1), (143, 16, 5), (221, 16, 3), (96577, 32, 1)):
            rows = projected_basis(n, u, r)
            cols = (0, 1, 3, 4)
            self.assertEqual(prod(row[j] for row,j in zip(rows, cols)), 1296000*r**6)
            for i, row in enumerate(rows):
                self.assertTrue(all(row[j] == 0 for j in cols[i+1:]))
                full = [v*n**max(2-j, 0) for j,v in enumerate(row)]
                self.assertFalse(any(any(v) for v in local_values(full, u, r).values()))
        a, b = clear_column([7, 8], [21, 0], 0)
        self.assertEqual((a[0], b[0]), (7, 0))
        self.assertEqual(abs(a[0]*b[1]-a[1]*b[0]), 168)

    def test_primitive_levels_and_modular_certificates(self):
        # For the nonconstant trace x-7, the level j gives the possible root x=7+jM.
        n, r, u, m = 143, 8, 7, 360*8**4
        for j in (-1, 0, 1):
            p = primitive_level([0, 0, -7, 1, 0], n, u, r, j, m)
            k = (7+j*m-u)//r
            self.assertEqual(sum(c*k**i for i,c in enumerate(p)), 0)
            self.assertTrue(all(has_local_root(p, prime) for prime in (2,3,5,7)))
        with self.assertRaises(ArithmeticError):
            primitive_level([0, 0, m, 0, 0], n, u, r, 1, m)
        self.assertFalse(has_local_root([1,0,1], 3))

    def test_coarse_small_lanes_against_direct_enumeration(self):
        for n,r in ((77,8), (143,8), (221,16), (77**2,16), (96577,32)):
            truth = trial_search(n)['pairs']
            _, weights = dickson_basis(n,2)
            for u in range(1, r, 2):
                run = search(n,r,u)
                expected = [pair for pair in truth if any(int(x)%r in (u, (-u)%r) for x in pair)]
                self.assertEqual(run['pairs'], expected)
                M, S, c = (int(run[k]) for k in ('modulus','spread','constant'))
                self.assertLessEqual((2*S)**4*12960*r**10, 2**11*prod(weights)*M**4)
                for j in range(run['first_level']-1, run['last_level']+2):
                    self.assertEqual(abs(j*M-c) <= S, run['first_level'] <= j <= run['last_level'])

    def test_signed_complete_small_comparison_and_large_coverage(self):
        report = json.loads((ROOT/'research/projected-quartic-levels.json').read_text())
        small = report['small']
        self.assertEqual(len(small), 5)
        coarse_pairs, fine_groups = set(), set()
        for row in small:
            p, q = (row['reports'][k] for k in ('parent','children'))
            self.assertEqual(p['pairs'], q['pairs'])
            coarse_pairs.update(tuple(pair) for pair in p['pairs'])
            fine_groups.update(min(signed_class(96577,64,int(u))) for u in q['residues'])
        self.assertEqual(coarse_pairs, {tuple(x) for x in trial_search(96577)['pairs']})
        self.assertEqual(len(fine_groups), 9)
        for row in report['deeper']:
            run, e = row['result'], row['exponent']
            n = int(report['full_size'][row['source']]['n'])
            self.assertEqual(len({min(signed_class(n,1<<614,1+j*(1<<e)))
                                  for j in range(1<<(614-e))}), 1<<(614-e))
            self.assertEqual(run['work']['lll_calls'],1)


class ProjectedLevelSieveTests(unittest.TestCase):
    def test_periodic_images_and_blocks_against_direct_products(self):
        n, modulus = 7*11, 360*8**4
        for coefficients in ([4,-11,13,2,5], [0,0,3,0,0], [0,0,0,0,0]):
            images = {}
            for p in (13,17,19):
                expected = {j for j in range(p) if any(
                    (sum(a*x**i for i,a in enumerate(coefficients))-modulus*j*x*x) % p == 0
                    for x in range(1,p))}
                self.assertEqual(level_image(coefficients,modulus,p), sum(1<<j for j in expected))
                images[p] = expected
            for first,last in ((-43,28),(-10,-10),(8,7),(0,98)):
                wanted = [j for j in range(first,last+1) if all(j%p in vals for p,vals in images.items())]
                for width in (1,9,17,29):
                    work = Counter()
                    result = list(block_survivors(coefficients,n,modulus,first,last,work,width,
                                                  (2,3,5,7,11,13,17,19)))
                    self.assertEqual(result, wanted)
                    self.assertEqual(work['level_positions_covered'], max(0,last-first+1))
                    if first <= last:
                        self.assertEqual(work['skipped_primes'], 5)

    def test_centered_complete_and_partial_groups(self):
        for n in (337, 11*13, 17**2, 59*61, 96577):
            lo,hi,*_ = windows(n)
            for u in (1,3,5,7):
                expected = {tuple(sorted((x,n//x))) for x in range(lo,hi+1)
                            if x%8 == u and n%x == 0 and lo <= n//x <= hi}
                result = centered_search(n,8,u)
                self.assertEqual({tuple(map(int,pair)) for pair in result['pairs']}, expected)
                self.assertEqual(result['unexamined_levels'],0)
        limited = centered_search(3376036549,8,1,max_levels=2)
        self.assertEqual(limited['work']['level_positions_covered'],2)
        self.assertEqual(limited['unexamined_levels'],limited['total_levels']-2)
        no_budget = centered_search(3376036549,8,1,max_levels=0)
        self.assertEqual(no_budget['unexamined_levels'],no_budget['total_levels'])

    def test_predeclared_inputs_and_scanning_budget(self):
        receipt = json.loads((ROOT/'research/projected-level-sieve.json').read_text())
        self.assertEqual((receipt['primary_exponent'],receipt['secondary_exponent'],receipt['residue']),
                         (604,600,1))
        for record in receipt['controls']:
            row, e = record['result'], record['exponent']
            n = int(row['n'])
            self.assertEqual(row['unexamined_levels'],0)
            self.assertEqual(row['work']['level_positions_covered'],row['total_levels'])
            self.assertEqual(row['work']['unit_evaluations'],6020)
            self.assertEqual(record['coverage'],covered_centered_groups(n,1<<e,1))
            self.assertEqual(record['lean_certificates'],len(row['pairs']))
            if record['source'] == 'unit-lane-fresh-2048':
                self.assertEqual(row['work']['empty_blocks'],row['work']['blocks'])
                self.assertEqual(row['work'].get('primitive_polynomials',0),0)
                self.assertEqual(record['remaining_cofactor'],str(n))
