import unittest
from math import gcd, isqrt

from experiments.centered_sum_quartic import centered_coordinates, probe, windows


class CenteredSumTests(unittest.TestCase):
    def test_centers_contain_every_equal_width_pair(self):
        for x in range(7, 97, 2):
            for y in range(x, 1 << x.bit_length(), 2):
                n = x*y
                if gcd(n, 30) > 1:
                    continue
                low, high, c, h, radius, s = windows(n)
                for z in (x, y):
                    self.assertTrue(low <= z <= high)
                    self.assertLessEqual(abs(z-c), radius)
                self.assertLessEqual(abs(x+y-h), 2*s)

    def test_empty_window(self):
        with self.assertRaisesRegex(ValueError, 'empty equal-width factor window'):
            windows(221)

    def test_trace_change_preserves_value(self):
        for x,y in ((17,31), (97,103), (211,179)):
            n = x*y
            _, _, c,h,_,s = windows(n)
            for trace in ([int(i == j) for j in range(5)] for i in range(5)):
                v = centered_coordinates(trace, n, c, h, s)
                t,z = x+y-h, x-c
                self.assertEqual(sum(a*b for a,b in zip(trace,(y*y,y,1,x,x*x))),
                                 sum(a*b for a,b in zip(v,(1,t,z,t*t-2*s*s,z*t))))

    def test_full_residue_search_agrees_with_divisors(self):
        for n in (143, 437, 10403, 96577):
            low, high, *_ = windows(n)
            e = probe(n)['radix_exponent']
            R = 1 << e
            groups = set()
            for u in range(1, R, 2):
                run = probe(n, u)
                groups.add(tuple(sorted((u,n*pow(u,-1,R)%R))))
                want = [[str(p),str(n//p)] for p in range(low, isqrt(n)+1)
                        if n%p==0 and n//p<=high and u in (p%R,(n//p)%R)]
                self.assertEqual(run['pairs'],want)
                self.assertFalse(any(any(v) for v in run['local_remainders'].values()))
            self.assertEqual(int(run['total_groups']),len(groups))
