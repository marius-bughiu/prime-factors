from math import gcd, prod
from unittest import TestCase
from unittest.mock import patch

from experiments.character_column_backends import MODES, compare, fold_diagnostic, reflection_axes
from experiments.character_growing_validation import costs
from experiments.growing_factorial import search
from experiments.mixed_ratio_heights import jacobi
from experiments.short_pascal_row import interval


class ColumnBackendTests(TestCase):
    def test_supplied_units_match_default_and_charge_validation(self):
        n = 645478771983487933
        offsets = (1, 5)
        for folded in (False, True):
            old = search(n, 50000, wheel=6, folded=folded, final_grid=True)
            same = search(n, 50000, wheel=6, folded=folded, final_grid=True,
                          bounds=interval(n), offsets=offsets)
            self.assertEqual(same['ranges'], old['ranges'])
            self.assertEqual(same['factor'], old['factor'])
            self.assertEqual(same['work'].pop('offset_validation_gcds'), len(offsets))
            self.assertEqual(old['work'].pop('wheel_residue_gcds'), 5)
            self.assertEqual(same['work'], old['work'])
        for invalid in [(), (1,1), (5,1), (1,6), (2,), (1.,), (True,)]:
            with self.assertRaises(ValueError):
                search(n, 10, wheel=6, offsets=invalid)
        for bounds in [(0,12),(50,40),(1,n),(1,5.0)]:
            with self.assertRaises(ValueError):
                search(n, None, bounds=bounds)

    def test_actual_complete_products_and_growing_coverage(self):
        n=1009*1019
        for wheel in (6,30):
            for clipped in (False,True):
                data,_=compare(n,clipped=clipped,wheel=wheel)
                p=data['period']
                lo,root=interval(n)
                b=1<<((n.bit_length()-1)//2)
                hi=min(2*b-1,n//b) if clipped else root
                values=[x for x in range(lo,hi+1) if gcd(x,p)==1 and
                        (not clipped or jacobi(data['d'], x)==data['sign'])]
                for mode in MODES:
                    run=data['runs'][mode]
                    if mode.startswith('complete'):
                        self.assertEqual(int(run['product']), prod(values)%n)
                        self.assertEqual(int(run['unvisited']),0)
                    else:
                        visited=[j for j in values if any(int(a)<=j<=int(b) for a,b in run['ranges'])]
                        self.assertEqual(int(run['visited']),len(visited))
                        self.assertEqual(gcd(n,prod(visited)),run['factor'])

    def test_mask_reflection_and_folded_root_collision_are_different(self):
        for period,d,sign,axes in [(60,-1,-1,[30]), (120,2,1,[0])]:
            offsets=[r for r in range(1,period) if gcd(r,period)==1 and jacobi(d,r)==sign]
            self.assertEqual(reflection_axes(period, offsets),axes)
        # A=98, stride=10, r=7, s=9 collapse at 101 despite differing offsets.
        diag=fold_diagnostic(101*113,10,[7,9],88,2,2,100)
        self.assertEqual(diag['root_checks'][0]['gcd'],'101')

    def test_no_fullsize_interpolation_or_unpaid_diagnostic(self):
        n=(1<<2047)+15
        with patch('experiments.character_column_backends.complete',side_effect=AssertionError):
            with patch('experiments.growing_factorial.search',side_effect=AssertionError):
                data,_=compare(n,clipped=False,max_work=40)
        for run in data['runs'].values():
            self.assertEqual(run['outcome'],'work_limit')
            self.assertEqual(run['unvisited'],data['candidates'])
            self.assertEqual(run['work'],{})
        self.assertTrue(all('gcd' not in r for r in data['checks']['root_checks']))

    def test_no_character_or_factor_before_interval_has_its_own_outcome(self):
        runs,_=compare(1009**2,clipped=True)
        self.assertEqual(runs['runs']['growing_forward']['outcome'],'no_witness')
        self.assertIsNone(runs['candidates'])
        runs,_=compare(3*101,clipped=True)
        self.assertEqual(runs['runs']['growing_forward']['factor'],3)

    def test_forward_shift_charges_count_weights_reciprocals_and_new_samples(self):
        # Degree 1 at 0,1 through last=4. Two weights, four reciprocals,
        # three new samples, one convolution with five decoded coefficients.
        work=dict(convolutions=1,convolution_input_coefficients=6,shifted_values=3,
                  peak_table_index=4,inversions=1,setup_gcds=1)
        plan=dict(selection={},mask_rebuild_gcds=0,mask_rebuild_jacobi=0)
        charges=costs(plan,dict(work=work))
        self.assertEqual(charges['table'],14)
        self.assertEqual(charges['interpolation'],8+8+9)
        self.assertEqual(charges['convolution'],6+10+1)

    def test_shortest_period_offsets_match_the_independent_complete_product(self):
        from experiments.separating_period import search as original
        for n in (1009*1019, 10007*12301):
            expected=original(n,wheel=30)
            plan,_=compare(n,clipped=True,least_period=True,wheel=30)
            self.assertEqual(plan['canonical'], expected['canonical'])
            for mode, run in plan['runs'].items():
                self.assertEqual(run['factor'], expected['factor'])
                if mode.startswith('complete'):
                    self.assertEqual(run['product'],expected['product'])
