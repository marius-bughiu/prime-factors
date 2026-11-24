from math import gcd, isqrt
import unittest

from experiments.seed_gap_sieve import allowed, candidate_bound, components, search, square_classes


class SeedGapSieveTests(unittest.TestCase):
    def test_cyclic_ranges_match_direct_square_table(self):
        m, residues = square_classes(143, components(5))
        squares = {x*x % m for x in range(m)}
        for v in range(1, 22):
            for size in (0, 1, m-1, m, m+1, 3*m+11):
                hits = list(allowed(size, v*v*pow(143, -1, m) % m, m, residues))
                self.assertEqual(hits, [h for h in range(1, size+1) if (h*143+v*v) % m in squares])

    def test_root_search_and_count_bound(self):
        for n in (143, 187, 221, 391, 437, 527, 709, 887*997):
            for s in (13, 48, 49, 112, 320):
                k = (min(s, (n-1)//2) - 1)//2
                found = False
                for v in range(1, isqrt(k)+1):
                    for h in range(1, k//(v*v)+1):
                        x = h*n+v*v
                        u = isqrt(x)
                        found |= u*u == x and 1 < gcd(u-v,n) < n
                result = search(n, s, 5)
                self.assertEqual(found, result['outcome']=='gap')
                self.assertLessEqual(result['square_tests'], candidate_bound(k,5)[2])
        self.assertEqual(search(15, 7, 5)['outcome'], 'wheel_gcd')
        self.assertIsNone(search(5, 7, 5)['factor'])
