import unittest
from itertools import combinations
from math import gcd

from experiments.short_pascal_row import interval
from experiments.twelve_rectangle import schedule, search
from experiments.twelve_residue_collision import directions


class RectangleTests(unittest.TestCase):
    def test_prefix_and_two_merged_offsets(self):
        for h in range(3,12):
            babies, giants = schedule(8417663,h,3,compressed=True)
            first = interval(8417663)[0] | 1
            offsets = set(babies) | {3,9}
            self.assertEqual(len(babies),h)
            self.assertEqual({g+s*b for g in giants for s in (-1,1) for b in offsets},
                             set(range(first,first+4*(h+2)*3,2)))

    def test_batched_splits_agree_with_individual_orientations(self):
        primes = (17,19,23,29,31,37,41,43,47,53)
        for p,q in combinations(primes,2):
            n = p*q
            for mode in ("squares","twelve","expanded_twelve"):
                left, right = schedule(n,6,5,compressed=mode == "expanded_twelve")
                grouped = mode != "squares"
                direct = grouped and any(1<gcd(x*x+3,n)<n for x in left+right)
                direct |= any(1<gcd(d*g+s*a,n)<n for b in left for g in right
                              for a,d in (directions(b) if grouped else [(b,1)]) for s in (-1,1))
                factor = search(n,6,5,mode)[0]
                with self.subTest(n=n,method=mode):
                    self.assertEqual(factor is not None,direct)
                    if factor:
                        self.assertIn(factor,(p,q))

    def test_smallest_rectangle_and_full_width_controls(self):
        n = 8417663
        self.assertIsNone(search(n,6,6,"squares")[0])
        self.assertEqual(search(n,6,6,"expanded_twelve")[0],2203)
        with self.assertRaises(ValueError):
            search(n,2,2,"expanded_twelve")
        with self.assertRaises(ValueError):
            search(n,6,0)


if __name__ == "__main__":
    unittest.main()
