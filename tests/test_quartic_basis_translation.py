import unittest

from experiments.quartic_basis_translation import search, translate
from experiments.quartic_divisor_window import evaluate, jet_basis


class QuarticBasisTranslationTests(unittest.TestCase):
    def test_translation_and_return_shift(self):
        for row in jet_basis(2501,1229):
            moved = translate(row,3)
            self.assertEqual(translate(moved,-3),row)
            for x in (-4,0,7):
                self.assertEqual(evaluate(moved,x),evaluate(row,x+3))

    def test_last_even_value_and_clipped_final_window(self):
        # The public range [40,50] has five odd candidates and six even values.
        for cap,expected in [(0,0),(1,3),(2,5),(30,5)]:
            result = search(2501,full=True,blocks=cap)
            self.assertEqual((result['range_lower'],result['range_upper']),(40,50))
            self.assertEqual((result['first_odd'],result['last_odd'],result['even_integers']),(41,49,6))
            self.assertEqual(result['visited_odd_integers'],expected)
            self.assertEqual(result['unvisited_odd_integers'],5-expected)
            self.assertEqual(result['exhausted'],cap>=2)
            self.assertEqual(result['divisors'],[41] if cap else [])

    def test_oversized_or_ineligible_ranges(self):
        for n,full,cap in [(4,True,1),(221,True,0),(49,False,3),(2501,True,-1)]:
            with self.assertRaises(ValueError):
                search(n,full=full,blocks=cap)
