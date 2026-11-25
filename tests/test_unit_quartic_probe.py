from collections import Counter
from itertools import product
import json
from math import factorial, gcd, isqrt, prod
import unittest

from experiments.affine_radix_holdout import trial_search
from experiments.gap_newton_lanes import dickson_basis, equation, gap_coordinates
from experiments.unit_quartic_probe import CONTENTS, ROOT, crt_nodes, local_values, probe, unit_basis


class UnitQuarticProbeTests(unittest.TestCase):
    def test_crt_nodes_minima_and_exact_trace_lattice(self):
        for n, radix, u in ((77, 8, 1), (143, 16, 5), (323, 32, 19)):
            nodes = crt_nodes(u, radix)
            modulus = 360*radix**4
            basis = unit_basis(n, u, radix)
            for j, a in enumerate(nodes):
                self.assertEqual((a-u-j*radix) % (8*radix**4), 0)
                self.assertEqual((a-1-j-j//2) % 9, 0)
                self.assertEqual((a-1-j-j//4) % 5, 0)
                fixed = gcd(modulus, prod(a-b for b in nodes[:j]))
                self.assertEqual(fixed, radix**j * CONTENTS[j])
                self.assertEqual(basis[j][j], modulus//fixed)
            vectors = list(product((-1, 0, 1), repeat=5)) + basis
            vectors.extend([[sum((h-i)*row[j] for h,row in enumerate(basis)) for j in range(5)]
                            for i in (1, 3)])
            for vector in vectors:
                residual = list(vector)
                for j in reversed(range(5)):
                    q, rem = divmod(residual[j], basis[j][j])
                    if rem:
                        break
                    residual = [x-q*y for x,y in zip(residual, basis[j])]
                full = [c*n**max(2-j, 0) for j,c in enumerate(vector)]
                checks = local_values(full, u, radix)
                self.assertEqual(not any(residual), not any(any(r) for r in checks.values()))

    def test_unit_grid_can_accept_a_polynomial_nonzero_on_nonunits(self):
        # The enumerated nodes force all units at both odd primes; x=3 is excluded.
        radix = 8
        p = [1]
        for root in (1, 2, 13, 14):
            p = [x-root*y for x,y in zip([0]+p, p+[0])]
        full = [8*radix**4*c for c in p]
        self.assertFalse(any(any(r) for r in local_values(full, 1, radix).values()))
        self.assertNotEqual(sum(c*3**j for j,c in enumerate(full)) % (360*radix**4), 0)

    def test_all_small_signed_lanes_against_trial_and_ordinary_dickson(self):
        for n, radix in ((143, 16), (221, 16), (77**2, 32), (13*17*19*23, 64)):
            transform, scales = dickson_basis(n, 2)
            all_pairs = trial_search(n)['pairs']
            for u in range(1, radix, 2):
                actual = probe(n, radix, u)
                expected = [pair for pair in all_pairs if any(int(x) % radix in (u, (-u) % radix)
                                                               for x in pair)]
                self.assertEqual(actual['pairs'], expected)
                self.assertFalse(any(any(v) for v in actual['local_remainders'].values()))
                ordinary = equation(n, u, radix, 2, [factorial(j) for j in range(5)],
                                    transform, scales, Counter())
                hits = set()
                lower, upper = max(2, isqrt((n-1)//2)+1), isqrt(2*n)
                for x in range(-upper, upper+1):
                    if abs(x) < lower or x % radix != u:
                        continue
                    k = (x-u)//radix
                    if sum(c*k**j for j,c in enumerate(ordinary)) == 0 and n % x == 0:
                        hits.add(tuple(sorted((abs(x), abs(n//x)))))
                self.assertEqual(hits, {tuple(map(int, pair)) for pair in expected})

    def test_stored_full_size_certificates_and_traces(self):
        artifact = json.loads((ROOT/'research/unit-quartic-probe.json').read_text())
        self.assertEqual(artifact['radix_exponent'], 614)
        self.assertEqual(len(artifact['rows']), 2)
        for case in artifact['rows']:
            report = case['result']
            n, r, u = (int(report[k]) for k in ('n', 'radix', 'u'))
            self.assertEqual((n.bit_length(), r, u), (2048, 1 << 614, 1))
            trace = list(map(int, report['trace_coefficients']))
            full = [c*n**max(2-j, 0) for j,c in enumerate(trace)]
            self.assertEqual(local_values(full, u, r), report['local_remainders'])
            self.assertTrue(all(all(v == 0 for v in values) for values in report['local_remainders'].values()))
            transform, scales = dickson_basis(n, 2)
            bound = sum(abs(v)*w for v,w in zip(gap_coordinates(trace, transform), scales))
            self.assertEqual(str(bound), report['weighted_l1'])
            self.assertLess(bound, 360*r**4)
            self.assertEqual(report['polynomial_degree'], 4)
            self.assertEqual(report['work']['lll_calls'], 1)
            self.assertEqual(int(report['unchecked_signed_groups']), 1 << 611)
            self.assertEqual(case['lean_certificates'], len(report['pairs']))
            for p, q in report['pairs']:
                self.assertEqual(int(p)*int(q), n)
        self.assertEqual([r['lean_certificates'] for r in artifact['rows']], [1, 0])
        self.assertEqual(artifact['rows'][1]['remaining_cofactor'], artifact['rows'][1]['result']['n'])
