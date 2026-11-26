from itertools import combinations
from math import comb, gcd, prod
import unittest

from experiments.geometric_sum_readout import coefficients, search


class GeometricSumReadoutTests(unittest.TestCase):
    def test_truncated_polynomial_against_omitted_products(self):
        for n, g, y, count in [(15, 2, 4, 0), (77, 3, 5, 6), (55, 2, 1, 9), (31, 4, 2, 5)]:
            powers = [pow(g, j, n) for j in range(count)]
            def omit(*exceptions):
                return prod(y-a for i, a in enumerate(powers) if i not in exceptions)
            c, linear, quadratic = coefficients(n, g, y, count)
            self.assertEqual(c, omit() % n)
            for i, z in enumerate([0, 1, -1]):
                first = [y*z-j*a for j, a in enumerate(powers)]
                expected_linear = sum(a*omit(j) for j, a in enumerate(first))
                expected_second = sum(-comb(j, 2)*a*omit(j) for j, a in enumerate(powers))
                expected_second += sum(first[j]*first[k]*omit(j, k)
                                       for j, k in combinations(range(count), 2))
                self.assertEqual(linear[i], expected_linear % n)
                self.assertEqual(quadratic[i], expected_second % n)

    def test_equal_cofactors_both_signs(self):
        for n, base, k, index in [(4453, 9, 12, 0), (30353, 22, 14, 17)]:
            run = search(n, base, 100)
            self.assertEqual(run['outcome'], 'equal_quotient_sum')
            self.assertEqual(run['winning_index'], index)
            self.assertEqual([entry['k'] for entry in run['equal_hits']], [k])
            self.assertIn(index, run['equal_hits'][0]['indices'])
            self.assertFalse(run['quotient_hits'])
            self.assertEqual(n % run['factor'], 0)
            self.assertEqual(search(n, base, 100, k-1)['outcome'], 'quotient_limit')

    def test_linear_and_quadratic_splits(self):
        self.assertEqual(search(33127, 2, 22)['outcome'], 'linear_sum')
        self.assertEqual(search(33127, 13, 22)['outcome'], 'linear_gcd')
        self.assertEqual(search(33127, 12, 22)['outcome'], 'quadratic_coefficient_gcd')
        run = search(34393, 23, 23)
        self.assertEqual(run['linear'], [0, 0, 0])
        self.assertEqual(run['quotient_hits'], [dict(k=9, factor='163'), dict(k=21, factor='211')])
        self.assertEqual(run['work']['quotient_gcds'], 48)

    def test_budget_and_base_gcd(self):
        run = search(34393, 23, 22)
        self.assertEqual(run['outcome'], 'term_limit')
        self.assertEqual(run['work']['unvisited_terms'], 23)
        self.assertEqual(run['work']['modular_powers'], 0)
        self.assertEqual(search(77, 7, 0)['factor'], 7)

    def test_composite_and_prime_inputs_do_not_report_false_splits(self):
        for n in range(9, 120, 2):
            for base in range(2, min(n, 14)):
                result = search(n, base, 100, 5)
                if result['factor'] is not None:
                    self.assertTrue(1 < result['factor'] < n)
                    self.assertEqual(gcd(n, result['factor']), result['factor'])


class BinarySumReadoutTests(unittest.TestCase):
    def test_compressed_classes_are_exact_and_disjoint(self):
        from experiments.geometric_sum_readout import _binary_classes
        for n in range(1, 32, 2):
            admitted, classes = _binary_classes(n)
            direct = {(x+y) % 32 for x in range(32) for y in range(32) if x*y % 32 == n}
            self.assertEqual(set(admitted), direct)
            for s in range(32):
                self.assertEqual(sum(s % step == r for r, step in classes), int(s in direct))

    def test_same_cap_fresh_draw(self):
        from experiments.affine_radix_holdout import draw_prime
        from experiments.geometric_sum_readout import search_binary
        primes = [draw_prime(side, 1, bits=16, seed=b'geometric-sum-binary-holdout-v1')
                  for side in (b'p', b'q')]
        n = prod(primes)
        self.assertEqual(n, 1599371087)
        self.assertEqual(search(n, 2, 1024)['outcome'], 'term_limit')
        run = search_binary(n, 2, 1024)
        self.assertEqual(run['total_terms'], '606')
        self.assertEqual(run['work']['terms'], 606)
        self.assertEqual(run['winning_sum'], str(sum(primes)))
        self.assertIn(run['factor'], primes)
        self.assertEqual(search_binary(n, 2, 605)['work']['modular_powers'], 0)

    def test_each_lane_matches_direct_signed_polynomial(self):
        from experiments.geometric_sum_readout import search_binary
        for n in [2173, 33127, 34393, 41567, 61937]:
            g = 2
            run = search_binary(n, g, 500)
            lower, upper = int(run['lower']), int(run['upper'])
            covered = []
            for lane in run['lanes']:
                stride, first, count = lane['stride'], int(lane['first']), int(lane['count'])
                sums = list(range(first, upper+1, stride))
                self.assertEqual(len(sums), count)
                covered.extend(sums)
                if count:
                    target = pow(g, n+1-first, n)
                    direct = prod((target - pow(g, s-first, n)) for s in sums) % n
                    self.assertEqual(lane['readout']['constant'], direct)
            self.assertEqual(sorted(covered), [s for s in range(lower, upper+1)
                                               if s % 32 in run['accepted_mod_32']])
            self.assertEqual(run['work']['terms'], len(covered))
            self.assertEqual(run['work']['modular_powers'],
                             run['work']['stride_powers']+run['work']['visited_lanes'])

    def test_multi_lane_cap_precedes_every_product(self):
        from experiments.geometric_sum_readout import search_binary
        run = search_binary(2173, 9, 1)
        self.assertEqual([int(lane['count']) for lane in run['lanes']], [1, 1])
        self.assertEqual(run['outcome'], 'term_limit')
        self.assertEqual(run['work']['unvisited_terms'], 2)
        self.assertEqual(run['work']['visited_lanes'], 0)
        self.assertEqual(run['work']['modular_powers'], 0)
        self.assertTrue(all('readout' not in lane for lane in run['lanes']))
