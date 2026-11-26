import unittest
from math import comb, gcd, prod

from experiments.short_pascal_blocks import search
from experiments.short_pascal_row import interval


class ShortPascalBlocksTests(unittest.TestCase):
    def test_exact_prefixes_on_clipped_periods_and_small_caps(self):
        for n in (3, 13*13, 101*107, 547*887, 811*937, 122821):
            lo, row = interval(n)
            for wheel in (1, 2, 30, 210):
                if gcd(n, wheel) != 1:
                    continue
                candidates = [x for x in range(lo, row+1) if gcd(x, wheel) == 1]
                for side in (0, 1, 3, 8, 17, 48, 256):
                    with self.subTest(n=n, wheel=wheel, side=side):
                        result = search(n, wheel, side)
                        used = result['checked_candidates']
                        self.assertEqual(used+int(result['remaining_candidates']), len(candidates))
                        self.assertEqual(result['last_checked'], str(candidates[used-1]) if used else None)
                        w = result['work']
                        self.assertLessEqual(max(w['roots'], w['points']), side)
                        self.assertEqual(used, w['head_terms']+w['roots']*w['points']+w['tail_terms'])
                        if used:
                            self.assertEqual(int(result['product_residue']), prod(candidates[:used]) % n)
                        if side >= int(result['target_side']):
                            self.assertEqual(used, len(candidates))

    def test_same_gcd_as_pascal_and_early_wheel_split(self):
        for p, q in ((17, 23), (101, 107), (101, 127), (1031, 2011)):
            n = p*q
            lo, row = interval(n)
            for wheel in (1, 2, 30, 210):
                result = search(n, wheel, 1024)
                self.assertEqual(result['factor'], gcd(n, comb(row, row-lo+1)))
                self.assertEqual(result['remaining_candidates'], '0')
        for n, wheel, wanted in ((35, 210, 5), (55, 30, 5), (21, 210, 3)):
            result = search(n, wheel, 0)
            self.assertEqual((result['outcome'], result['factor']), ('wheel_factor', wanted))
            self.assertEqual(result['work']['roots'], 0)
        self.assertIsNone(search(5, 30, 0)['factor'])

    def test_fresh_39_bit_product_uses_both_edges_and_the_tree(self):
        result = search(534799409953, 30, 240)
        self.assertEqual(result['factor'], 697819)
        self.assertEqual((result['checked_candidates'], result['remaining_candidates']), (55204, '0'))
        work = result['work']
        self.assertEqual((work['roots'], work['points']), (240, 229))
        self.assertEqual(work['head_terms'] + work['tail_terms'], 244)

    def test_off_promise_whole_gcd_is_refined(self):
        # Several small factors divide different entries of the retained interval.
        case = search(3**3*5*7*11, 2, 100)
        self.assertEqual(case['outcome'], 'refined_gcd')
        self.assertEqual((int(case['product_residue']), int(case['n']) % case['factor']), (0, 0))
        self.assertGreater(case['work']['refinement_gcds'], 0)
