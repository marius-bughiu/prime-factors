import unittest
from math import gcd

from experiments.reciprocal_sum_slice import WIDTH, block, endpoints, search, square_table, wheel_count


class ReciprocalSumSliceTests(unittest.TestCase):
    def test_literal_small_slices_and_factors(self):
        table = square_table()
        for n in range(3, 4000, 2):
            if n % 211 == 0:
                continue
            a,b = endpoints(n)
            self.assertLess(2500*(a-1)**2, 2401*n)
            self.assertLessEqual(2401*n, 2500*a*a)
            if a>b:
                continue
            positions, lookups, live = block(n,a,b,table)
            sums = range(b+(n+b-1)//b, a+n//a+1)
            sums = [s for s in sums if (s-n-1)%4==0]
            direct = [x for x in range(a,b+1) if x%2 and x%211!=0
                      and any(x*(s-x)%211==n%211 for s in sums)]
            self.assertEqual(sorted(positions), direct)
            self.assertEqual(len(sums), lookups)
            self.assertEqual(live, [s for s in sums if table[(s*s-4*n)%211]])
            self.assertTrue(all(d in positions for d in range(a,b+1) if n%d==0))
            self.assertEqual(wheel_count(a,b), sum(gcd(x,422)==1 for x in range(a,b+1)))

    def test_target_bound_and_block_ranges(self):
        for n in (1000003*1900009, (2**1600)+51, (2**2047)+987):
            a,b=endpoints(n)
            for start in (a, max(a,b-WIDTH+1)):
                end=min(start+WIDTH-1,b)
                found, count, _=block(n,start,end,square_table())
                self.assertLessEqual(len(found),36)
                self.assertLessEqual(count,9)
                if end-start+1==WIDTH:
                    self.assertEqual(wheel_count(start,end),420)
        n=1009*1013
        solved=search(n,2)
        self.assertEqual((solved['factor'],solved['fermat_factor']), (1009,'1009'))
        self.assertEqual(search(n,0)['untested_blocks'],solved['blocks_needed'])
        self.assertEqual(search(211*223,2)['factor'],211)
